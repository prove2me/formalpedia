-- Prove2me | Theorems.Thm_FewInnerTSP_lemma_4_5
-- name    : FewInnerTSP.lemma_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T03:33:44.92322+00:00
-- url     : https://prove2.me/theorems/bdf9e58a-8dd6-4d81-b08d-2610b6a752cc
-- title:
--   Lemma 4.5 (A constructible simultaneous bound)
-- statement:
--   In normalized coordinates, let $A$ be $a\ge1$ core points and $H$ points on the boundary of the convex hull of the skeleton vertices $w_0,\dots,w_{m-1}$ (in cyclic order), with $|A|+|H|\le N_0$ and $m\le N_0$, and $V=A\cup H$. Let $\mu=1/[100(N_0+1)^3]$ and $J=\lceil\log_2(1/\mu)\rceil+1$. There are constants $C,d$ and one admissible real-RAM program, fixed before the input, which on the input $(N_0,a,h,m,A,H,w)$ halts within $C(N_0+2)^d$ steps and outputs one number $t$ such that:
--
--   1. $t\in[1,3]$;
--   2. (10): $E_A(t)\le C\sqrt a$ and $E_H(t)\le C\log^2(N_0+2)$;
--   3. (11): $\mathrm{dist}_\infty(v,\partial\sigma_t)=\bigl|\|v\|_\infty-t/2\bigr|\ge\mu$ for all $v\in V$;
--   4. only $O(\log N_0)$ dyadic scales are used: $J\le C\log(N_0+2)$, and no frame of a scale $j>J$ that is active at $t$ contains a point of $V$, so the charges receive nothing from those scales;
--   5. no supporting line $x_r=\pm t/2$ of $\sigma_t$ contains a skeleton edge $w_iw_{i+1}$.
--
--   The selected separator works simultaneously for both populations, and its clearance rules out short straddling edges.
--
--   Differences from the source:
--   - reading: a real-arithmetic model supporting exact Euclidean distances and exact comparison of finite sums of edge costs (no instruction set named) → the published real RAM MatMulTimeLP.RealRAM restricted by Admissible: rational literals, no draws, rsqrt allowed, every executed instruction (index bookkeeping and input reads included) costing 1; reason: the fewest primitives give the strongest statement under an existential program; comparing a sum costs its additions plus one comparison, which no model with those primitives undercuts
--   - encoding: polynomial arithmetic complexity → (T+1) ≤ C (N₀+2)^d with C, d fixed before the input; the output is the one cell t; reason: O-notation with the constants before the input
--   - encoding: uses only O(log N0) dyadic scales → J = ⌈log₂(1/µ)⌉ + 1 ≤ C log(N₀+2), and no active frame at a scale j > J contains a point of V; reason: App. B.3's truncation statement, which is what 'uses only' those scales means
--   - generalization: the printed conclusion (10), (11) → an added clause 5: no supporting line of σ_t contains a skeleton edge; reason: App. B.3's construction also secures it ('avoid the finitely many parameters at which a square supporting line coincides with a skeleton edge'), and Theorem 4.1's skeleton count uses it
--   - generalization: H the skeleton vertices of the state → H any set of points on the frontier of the hull of the skeleton vertices; reason: contains the page's case
--   - encoding: dist∞(v, ∂σt) ≥ µ → |max(|v₀|, |v₁|) − t/2| ≥ µ; reason: for the sup-norm ball centered at 0 the two are equal
--   - encoding: V = A ⊔ H with N0 the global vertex bound → duplicate-free lists of normalized points with |A| + |H| ≤ N₀ and m ≤ N₀, a ≥ 1; reason: the input of the construction; N₀ bounds every vertex count
-- source:
--   Li, Ma, Gong, Exact Euclidean TSP with Few Interior Points: A Square-Root Exponent, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 4.5, p.8 (PDF p.10); proof App. B.3, p.17 (PDF p.19)

import Mathlib
import Definitions.Def_FewInnerTSP_Charges
import Definitions.Def_FewInnerTSP_Admissible
import Definitions.Def_FewInnerTSP_Layouts

namespace FewInnerTSP

open scoped ENNReal

open Classical in
/-- **Lemma 4.5 (A constructible simultaneous bound).** Li, Ma, Gong, *Exact Euclidean TSP with Few
Interior Points: A Square-Root Exponent*, STOC 2027 submission (manuscript sha256 6541f631…), Lemma 4.5,
p.8 (PDF p.10), proof App. B.3, p.17 (PDF p.19): "One can deterministically select t ∈ [1, 3] such that
EA(t) = O(√a), EH(t) = O(log²(N0 + 2)), (10) dist∞(v, ∂σt) ≥ µ for all v ∈ V, (11) where
µ = 1/[100(N0 + 1)³]. The construction has polynomial arithmetic complexity and uses only O(log N0)
dyadic scales."

In normalized coordinates, with `A` (`a ≥ 1` core points) and `H` (skeleton points on the boundary of the
convex hull of the skeleton vertices `w 0, …, w (m−1)`), `|A| + |H| ≤ N₀` and `m ≤ N₀`: there are
constants `C, d` and one admissible program, fixed before the input, that on the input
`[N₀, a, h, m, A, H, w]` halt within `C (N₀ + 2)^d` steps and output one cell `t` with
1. `t ∈ [1, 3]`;
2. (10): `E_A(t) ≤ C √a` and `E_H(t) ≤ C log²(N₀ + 2)`;
3. (11): `dist∞(v, ∂σ_t) = |‖v‖∞ − t/2| ≥ µ` for every `v ∈ V = A ∪ H`;
4. only `O(log N₀)` scales: `J = ⌈log₂(1/µ)⌉ + 1 ≤ C log(N₀ + 2)`, and no active frame of a scale
   `j > J` contains a point of `V`, so the charges receive nothing from those scales;
5. no supporting line `x_r = ±t/2` of `σ_t` contains a skeleton edge `w_i w_{i+1}`.

**Formalization Note** Clause 5 is the property App. B.3's sweep also secures ("avoid the finitely many
parameters at which a square supporting line coincides with a skeleton edge"), used by Theorem 4.1; it is
added to the printed conclusion. The skeleton points are given in cyclic order. -/
theorem lemma_4_5 :
    ∃ (C : ℝ) (d : ℕ), 0 < C ∧ ∃ Prog : MatMulTimeLP.Program, Admissible Prog ∧
      ∀ (N0 m : ℕ) (w : Fin m → Pt) (la lh : List Pt), la.Nodup → lh.Nodup →
        1 ≤ la.length → la.length + lh.length ≤ N0 → m ≤ N0 →
        (∀ x ∈ lh, x ∈ frontier (convexHull ℝ (Set.range w))) →
        ∀ ω : MatMulTimeLP.Tape, ∃ (T : ℕ) (t : ℝ),
          MatMulTimeLP.HaltsAt Prog (chargeLayout N0 la lh w) ω T ∧
          (T : ℝ) + 1 ≤ C * ((N0 : ℝ) + 2) ^ d ∧
          OutputIs Prog (chargeLayout N0 la lh w) ω T [t] ∧
          t ∈ Set.Icc (1 : ℝ) 3 ∧
          charge la.toFinset t ≤ ENNReal.ofReal (C * Real.sqrt (la.length : ℝ)) ∧
          charge lh.toFinset t ≤ ENNReal.ofReal (C * Real.log ((N0 : ℝ) + 2) ^ 2) ∧
          (∀ v ∈ la ++ lh, clearance N0 ≤ |max |v 0| |v 1| - t / 2|) ∧
          ((scaleCut N0 : ℝ) ≤ C * Real.log ((N0 : ℝ) + 2) ∧
            ∀ j : ℕ, scaleCut N0 < j → ∀ i l : ℤ, FrameActive t j i l →
              ∀ v ∈ la ++ lh, v ∉ frame j i l) ∧
          ∀ (i : Fin m) (r : Fin 2),
            ¬ (|w i r| = t / 2 ∧ w (finRotate m i) r = w i r) := by sorry

end FewInnerTSP
