-- Prove2me | Theorems.Thm_FairFacilityLoc_proposition_3_15
-- name    : FairFacilityLoc.proposition_3_15
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:25.954504+00:00
-- url     : https://prove2.me/theorems/5a0c3935-5398-47b7-8cdc-e24f13b47e87
-- title:
--   Proposition 3.15 — dominating vectors and the budget of a coordinate
-- statement:
--   Let $W,x,z$ be normalized with $Q_r(a)\le K_r$ for all $a\in W$ and all $r$, for $d\in\{1,2,3\}$.
--
--   For $d\in\{2,3\}$, every capacity is positive. If $K_r>0$, a dominating vector $a$ of coordinate $r$, with total mass $A=A(N;a)$, satisfies
--   $$\sigma(N^-_r;a)=K_r,\quad K_r\le A^2,\quad(1-b_d)A^2\le2K_r,\quad Q_k(a)\le K_k\ (k=1,\dots,d),\quad L^-(a)\le1.$$
--   If moreover $z_r>0$, it satisfies the budget of coordinate $r$:
--   $$\mathcal C+(1+b_d)(1+z_r)A\ \ge\ (1+z_r)\bigl(1-(1-b_d)z_r\bigr)A^2+z_r(1+2z_r)K_r.$$
--
--   The budgets relate the capacities of different coordinates, which is what the bound $\mathcal C\le d$ needs.
--
--   Differences from the source:
--   - generalization: a linear group with weight $w_j$ → a nonnegative weight vector $a\in\mathbb R^N$; reason: the proof of Proposition 3.27 (p.48) re-runs this statement for weight vectors; a linear group is $a=w_j\mathbf 1_{G_j}$
--   - generalization: normalized coordinates of a mechanism output, where Lemma 3.9 holds → any normalized family with $Q_r(a)\le K_r$ for all $a,r$ (CapacityCondition); reason: the proof uses the mechanism only through this inequality; Lemma 3.9 (`lemma_3_9`) supplies it for a mechanism output
--   - encoding: the normalization (3.2), with the output at the origin → the structure IsNormalized; reason: the fields are the hypotheses (3.2) for a finite nonnegative family with a vector of positive mass
--   - encoding: $d\le 3$ → $1\le d\le 3$; reason: dimensions are positive throughout the paper; (1.2) lists $1\le d\le3$
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Proposition 3.15, (3.15), (3.16), p.33 (PDF p.35); family form p.49 (PDF p.51)

import Mathlib
import Definitions.Def_FairFacilityLoc_penalty
import Definitions.Def_FairFacilityLoc_sideLength
import Definitions.Def_FairFacilityLoc_IsNormalized

namespace FairFacilityLoc

/-- **Proposition 3.15** (Yan, Zhou, manuscript, sha256 642a1268…, p.33, PDF p.35), with (3.15) and the budget (3.16).
For `d ∈ {2, 3}`, every capacity is positive. If `K_r > 0`, a dominating vector `a` of coordinate `r` satisfies
`σ(N⁻_r; a) = K_r`, `K_r ≤ A²`, `(1 − b_d) A² ≤ 2 K_r`, `Q_k(a) ≤ K_k` for every `k`, and `L⁻(a) ≤ 1`, with
`A = A(N; a)`. If moreover `z_r > 0`, then
`C + (1 + b_d)(1 + z_r) A ≥ (1 + z_r)(1 − (1 − b_d) z_r) A² + z_r (1 + 2 z_r) K_r`.

**Formalization Note.** Only the first sentence is restricted to `d ∈ {2, 3}`; the rest holds for `d ∈ {1, 2, 3}`, and
Proposition 3.17 uses it at `d = 1`. Stated for weight families, as on p.49. `CapacityCondition` is the conclusion of
Lemma 3.9. -/
theorem proposition_3_15 {n d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {W : Finset (Fin n → ℝ)}
    {x : Fin n → GeoSemialgCSP.E d} {z : GeoSemialgCSP.E d} (hN : IsNormalized W x z)
    (hC : CapacityCondition (penalty d) W x) :
    ((d = 2 ∨ d = 3) → ∀ r, 0 < capacity (penalty d) W x r) ∧
      ∀ (r : Fin d) (a : Fin n → ℝ), IsDominating (penalty d) W x r a →
        0 < capacity (penalty d) W x r →
        (weightScore (penalty d) a (nonposSide x r) = capacity (penalty d) W x r ∧
          capacity (penalty d) W x r ≤ mass a Finset.univ ^ 2 ∧
          (1 - penalty d) * mass a Finset.univ ^ 2 ≤ 2 * capacity (penalty d) W x r ∧
          (∀ k, posScore (penalty d) x a k ≤ capacity (penalty d) W x k) ∧
          nonposLength x z a ≤ 1) ∧
        (0 < z r →
          (1 + z r) * (1 - (1 - penalty d) * z r) * mass a Finset.univ ^ 2 +
              z r * (1 + 2 * z r) * capacity (penalty d) W x r ≤
            weightedCapacity (penalty d) W x z +
              (1 + penalty d) * (1 + z r) * mass a Finset.univ) := by sorry

end FairFacilityLoc
