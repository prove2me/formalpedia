-- Prove2me | Theorems.Thm_DoublingMST_lemma_4_1
-- name    : DoublingMST.lemma_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:43:03.739798+00:00
-- url     : https://prove2.me/theorems/23339693-7772-4413-bb9a-b24b0bb09526
-- title:
--   Lemma 4.1 — Algorithm 2 returns a $(1+2^{O(\mathrm{ddim})}\epsilon)$-approximate MST
-- statement:
--   There is an absolute constant $C>0$ with the following property. Assume $|X|\ge2$ and minimum interpoint distance $>1$, and let $\epsilon=2^{-K}$ with $K\ge2$. Let $N$ be a net hierarchy, $\Psi$ an output of Algorithm 1 with $t=32$, and $G$ any graph that Lines 1–15 of Algorithm 2 can build from them. Then
--
--   1. $G$ has a minimum spanning tree (in particular $G$ contains a spanning tree of $X$);
--   2. every minimum spanning tree $T$ of $G$ satisfies
--   $$w(T)\le\bigl(1+2^{C\operatorname{ddim}(X)}\epsilon\bigr)\,\mathrm{MST}(X).$$
--
--   This is the approximation half of Theorem 1.1.
--
--   Differences from the source:
--
--   - encoding: an n-point metric space (X, d) → points Fin n with d : Fin n → Fin n → ℝ satisfying IsMetric; reason: finite metric spaces up to relabelling; same instances
--   - encoding: the standing assumption |X| ≥ 2 of §2 (p.11) → hypothesis 2 ≤ n on the number of points; reason: the source assumes it throughout; it excludes only the one-point space
--   - encoding: the §2.1 standing assumption that the minimum interpoint distance of X is greater than 1 (p.12) → hypothesis MinDistGtOne d; reason: the source assumes it throughout §§2.1–4 (it is what makes level-0 balls singletons)
--   - encoding: ϵ ∈ (0, 1/2) a power of 2 (§4.1: "we may assume that ϵ is a power of 2") → ϵ = 2^{−K} with K ≥ 2; reason: §4.1's standing assumption; the powers of 2 in (0, 1/2) are exactly these
--   - reading: Algorithm 2 returns → for every net hierarchy, every run of Algorithm 1, every critical level, every choice of the argmins and every MST of the resulting G; reason: the algorithm leaves these choices open; the bound holds for all of them
--   - reading: returns MST(G) → the conclusion also states that G has an MST; reason: Line 16 presupposes it; the proof shows G contains a spanning tree (p.20)
--   - reading: 2^{O(ddim)} → ∃ C > 0, chosen before the space, with factor 2^{C · ddim(X)}; reason: the standard meaning of the O
--   - generalization: §2.2 (p.13): "we can assume henceforth that the minimum interpoint distance of X is greater than 1 and the diameter of X is ∆ ≤ n^{10}/ϵ" → no upper bound on the diameter; minimum distance > 1 is kept; reason: the proof (pp.20–23) never uses the bound (it uses only 2^L < 64 diam(X), p.21), and the statement specializes to the source's by adding the bound
-- source:
--   Höckendorff, Hommelsheim, Sohler, Yue, Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics, STOC 2027 submission (manuscript sha256 4855d6b39caaedcdac985f11ec23b5833ef4686c045f97ef13a21bdff2fbe759), Lemma 4.1, p.19 (PDF p.21); §4.1, p.18 (PDF p.20); proof pp.20–24

import Mathlib
import Definitions.Def_DoublingMST_IsMetric
import Definitions.Def_DoublingMST_MinDistGtOne
import Definitions.Def_DoublingMST_ddim
import Definitions.Def_DoublingMST_mstWeight
import Definitions.Def_DoublingMST_IsMSTOf
import Definitions.Def_DoublingMST_IsAlg2Graph
open scoped Classical

namespace DoublingMST

/-- **Lemma 4.1 (approximation guarantee of Algorithm 2).**
Höckendorff–Hommelsheim–Sohler–Yue, *Tight Bounds for (1+ϵ)-Approximation for Minimum Spanning Trees in Doubling Metrics*, STOC 2027 submission (manuscript sha256 4855d6b3…be759), Lemma 4.1, p.19 (PDF p.21): "Algorithm 2 returns a (1 + 2^{O(ddim)}ϵ)-approximate MST."
§4.1, p.18: "Throughout the section, we may assume that ϵ is a power of 2."

There is an absolute `C > 0` such that, under the standing assumptions of §2.1 (a metric on `n ≥ 2`
points, minimum interpoint distance `> 1`), for every `ϵ = 2^{−K}` with `K ≥ 2`, every net hierarchy
`H`, every output `Ψ` of Algorithm 1 (t = 32) and every graph `G` that Lines 1–15 of Algorithm 2 can
build from them:
1. `G` has a minimum spanning tree (in particular `G` is connected);
2. every minimum spanning tree `T` of `G` has `w(T) ≤ (1 + 2^{C·ddim(X)} ϵ) · MST(X)`.

**Formalization Note.** "Algorithm 2 returns" quantifies over every run: every `(H, Ψ, G)` that
`IsAlg2Graph` allows and every MST of `G` (Line 16). `ϵ = 2^{−K}`, `K ≥ 2`, is §4.1's standing
assumption together with `ϵ ∈ (0, 1/2)`. -/
theorem lemma_4_1 : ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 2 ≤ n → ∀ d : Fin n → Fin n → ℝ, IsMetric d →
    MinDistGtOne d → ∀ K : ℕ, 2 ≤ K → ∀ (H : NetHierarchy d)
    (Ψ : Finset ((Fin n × ℕ) × (Fin n × ℕ))) (G : Finset (Sym2 (Fin n))), IsAlg2Graph H K Ψ G →
      (∃ T : Finset (Sym2 (Fin n)), IsMSTOf d G T) ∧
      ∀ T : Finset (Sym2 (Fin n)), IsMSTOf d G T →
        treeWeight d T ≤ (1 + (2 : ℝ) ^ (C * ddim d) * (2 : ℝ) ^ (-(K : ℤ))) * mstWeight d := by sorry

end DoublingMST
