-- Prove2me | Theorems.Thm_DoublingMST_lemma_4_3
-- name    : DoublingMST.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:12.324013+00:00
-- url     : https://prove2.me/theorems/2784db32-23c5-491f-8c17-6c247a292524
-- title:
--   Lemma 4.3 — Algorithm 2 runs in time $2^{O(\mathrm{ddim})}n(\log n+\epsilon^{-1}\log(1/\epsilon))$
-- statement:
--   There is a program $P$ of the real RAM of Definition 2.1 such that for every $c_0>0$ there is $C>0$ with the following property. For every $n\ge2$, every injective labelling $\iota$ of the points by integers, every metric $d$ with minimum interpoint distance $>1$, every $K\ge2$ and $\epsilon=2^{-K}$ with $\operatorname{diam}(X)\le c_0n^{10}/\epsilon$, the program started on $\iota$, $\epsilon$ and the exact diameter of $X$, with distance oracle $d$:
--
--   1. halts within $2^{C\operatorname{ddim}(X)}\,n\,(\log_2n+\epsilon^{-1}\log_2(1/\epsilon))$ steps;
--   2. outputs $n-1$ pairs of labels;
--   3. the edges they name form a minimum spanning tree of some graph $G$ that Lines 1–15 of Algorithm 2 can build, for some net hierarchy and some output of Algorithm 1 with $t=32$.
--
--   This is the running-time half of Theorem 1.1, under the normalizations of §2.2. The diameter is an input as in footnote 8, p.51 ("We assume the diameter is known in advance for ease of presentation"); Theorem 1.1 is not given it.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - reading: Algorithm 2 runs in time T → a program of the machine of Definition 2.1 halts within T steps with output an MST of a graph G that Lines 1–15 can build; reason: time is measured on the model of Definition 2.1 (Section 1.1, p.2)
--   - encoding: "we assume wlog that the minimum interpoint distance of X is greater than 1" (proof, p.24) → hypothesis MinDistGtOne d; reason: the assumption of the proof
--   - reading: "the diameter of X is ∆ ≤ O(n^{10}/ϵ)" (proof, p.24) → for every c₀ > 0, chosen after the program, hypothesis diam(X) ≤ c₀ n^{10}/ϵ, with C depending on c₀; reason: covers every constant of the O; the program does not depend on c₀
--   - reading: footnote 8, p.51: "We assume the diameter is known in advance for ease of presentation", and Line 1 of Algorithm 2 builds the hierarchy of §2.1 with L = ⌈log ∆⌉ + 4 → the program also receives the exact diameter ∆ in real register 1; the rest of the input is as in the goal; reason: the footnote's constant-approximation implementation builds a hierarchy with another L, so its run is not an Algorithm 2 run on a hierarchy of §2.1; the conclusion names such a run, so the presentation's assumption is what makes the statement the printed one
--   - encoding: ϵ a power of 2 (§4.1), ϵ ∈ (0, 1/2) → ϵ = 2^{−K} with K ≥ 2; the program is given ϵ, not K; reason: §4.1's standing assumption
--   - reading: 2^{O(ddim)} → ∃ C > 0 (depending only on c₀) with factor 2^{C · ddim(X)}; reason: the standard meaning of the O
--   - reading: "ordinary RAM operations" on integer registers → integer constants, copy, +, −, increment, decrement, comparison and indirect load/store over unbounded ℤ; reason: a subset of every ordinary RAM's operations, so an existence claim over it is the stronger one
--   - encoding: a list of n − 1 pairs of point labels stored in integer registers → integer memory cells I[−2i−1], I[−2i−2] at halt; input labels in I[0..n−1], n in p[0], ϵ in r[0], ∆ in r[1]; reason: a fixed layout
--   - encoding: oracle given two point labels → an oracle call on a non-label integer leaves the run stuck; reason: excludes an undefined case
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 4.3, p.24 (PDF p.26), with the assumptions of its proof, p.24, and §4.1, p.18 (PDF p.20); proof pp.24–26

import Mathlib
import Definitions.Def_DoublingMST_Machine
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_MinDistGtOne
import Definitions.Def_DoublingMST_ddim
import Definitions.Def_DoublingMST_diam
import Definitions.Def_DoublingMST_decodeEdges
import Definitions.Def_DoublingMST_IsMSTOf
import Definitions.Def_DoublingMST_IsAlg2Graph
open scoped Classical

namespace DoublingMST

/-- **Lemma 4.3 (running time of Algorithm 2), on the machine of Definition 2.1.**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 4.3, p.24 (PDF p.26): "Algorithm 2 runs in time 2^{O(ddim)}n(log n + ϵ^{−1} log(1/ϵ))."
Its proof, p.24: "Throughout the proof, we assume wlog that the minimum interpoint distance of X is
greater than 1 and the diameter of X is ∆ ≤ O(n^{10}/ϵ)." §4.1, p.18: "we may assume that ϵ is a
power of 2". Appendix B.2, p.51, footnote 8: "We assume the diameter is known in advance for ease
of presentation."; Line 1 of Algorithm 2 builds the hierarchy of §2.1, whose `L = ⌈log ∆⌉ + 4`
depends on the exact diameter.

There is a program `P` of the real RAM of Definition 2.1 such that for every `c₀ > 0` there is a
`C > 0` with the following property. For every `n ≥ 2`, every injective labelling `ι` of the points
by integers, every metric `d` with minimum interpoint distance `> 1`, every `K ≥ 2` and
`ϵ = 2^{−K}` with `diam(X) ≤ c₀ n^{10}/ϵ`, the program started on `(ι, ϵ, diam(X))` with oracle `d`:
1. halts within `2^{C·ddim(X)} · n · (log₂ n + ϵ^{−1} log₂(1/ϵ))` steps;
2. outputs `n − 1` pairs of labels naming a spanning tree `T`;
3. `T` is a minimum spanning tree of some graph `G` that Lines 1–15 of Algorithm 2 can build, for
   some net hierarchy `H` and some output `Ψ` of Algorithm 1 with `t = 32`.

**Formalization Note.** The program is fixed before `c₀` and the input; only the constant depends on
`c₀`, which covers every reading of the `O(n^{10}/ϵ)`. The program receives the labels, `ϵ` and the
exact diameter (footnote 8), and not `K`, `c₀` or ddim. A program with only a constant approximation
of the diameter, as footnote 8 says suffices for an implementation, would build a hierarchy with
another `L`, which is not a `NetHierarchy` of §2.1 and need not yield an `IsAlg2Graph`; the goal
theorem is the statement without the diameter. Machine conventions: `Definitions.Def_DoublingMST_Machine`. -/
theorem lemma_4_3 : ∃ P : Program, ∀ c₀ : ℝ, 0 < c₀ → ∃ C : ℝ, 0 < C ∧
    ∀ (n : ℕ), 2 ≤ n → ∀ ι : Fin n → ℤ, Function.Injective ι →
    ∀ d : Fin n → Fin n → ℝ, IsMetric d → MinDistGtOne d →
    ∀ K : ℕ, 2 ≤ K → ∀ ϵ : ℝ, ϵ = (2 : ℝ) ^ (-(K : ℤ)) →
      diam d Finset.univ ≤ c₀ * (n : ℝ) ^ 10 / ϵ →
      ∃ out : List (ℤ × ℤ),
        HaltsWithinKnownDiam P ι d ϵ (diam d Finset.univ)
          ((2 : ℝ) ^ (C * ddim d) * n * (Real.logb 2 n + ϵ⁻¹ * Real.logb 2 (1 / ϵ))) out ∧
        out.length = n - 1 ∧ (∀ p ∈ out, (∃ a, ι a = p.1) ∧ (∃ b, ι b = p.2)) ∧
        ∃ (H : NetHierarchy d) (Ψ : Finset ((Fin n × ℕ) × (Fin n × ℕ)))
          (G : Finset (Sym2 (Fin n))), IsAlg2Graph H K Ψ G ∧ IsMSTOf d G (decodeEdges ι out) := by sorry

end DoublingMST
