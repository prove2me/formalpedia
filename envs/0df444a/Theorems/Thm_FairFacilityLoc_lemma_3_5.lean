-- Prove2me | Theorems.Thm_FairFacilityLoc_lemma_3_5
-- name    : FairFacilityLoc.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:25.592686+00:00
-- url     : https://prove2.me/theorems/674544c3-37a7-419c-8a2f-4db4ce422560
-- title:
--   Lemma 3.5 — the support bound
-- statement:
--   In normalized coordinates, every weight vector $a\in W$ satisfies the support bound
--   $$L^-(a)\le C_a(z)\le1,\qquad C_a(0)\le L^+(a)+\sqrt{1-L^-(a)^2}.$$
--
--   It bounds the effect at the output by the side lengths, which reduces the ratio to a bound on the side-length gap.
--
--   **Formalization Note** For a linear group $a=w_j\mathbf 1_{G_j}$, $C_a=E_j$ and $L^\pm(a)=L^\pm_j$.
--
--   Differences from the source:
--   - generalization: a linear group with weight $w_j$ → a nonnegative weight vector $a\in\mathbb R^N$; reason: the proof of Proposition 3.27 (p.48) re-runs this statement for weight vectors; a linear group is $a=w_j\mathbf 1_{G_j}$
--   - encoding: the normalization (3.2), with the output at the origin → the structure IsNormalized; reason: the fields are the hypotheses (3.2) for a finite nonnegative family with a vector of positive mass
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Lemma 3.5, (3.4), p.22 (PDF p.24); family form p.48 (PDF p.50)

import Mathlib
import Definitions.Def_FairFacilityLoc_sideLength
import Definitions.Def_FairFacilityLoc_IsNormalized

namespace FairFacilityLoc

/-- **Lemma 3.5, the support bound** (Yan, Zhou, manuscript, sha256 642a1268…, p.22, PDF p.24), for a weight vector
`a` of a normalized family: `L⁻(a) ≤ C_a(z) ≤ 1` and `C_a(0) ≤ L⁺(a) + √(1 − L⁻(a)²)`.

**Formalization Note.** A linear group is the vector `a = w_j 1_{G_j}`. The root's argument is nonnegative by the
first clause. -/
theorem lemma_3_5 {n d : ℕ} {W : Finset (Fin n → ℝ)} {x : Fin n → GeoSemialgCSP.E d} {z : GeoSemialgCSP.E d}
    (hN : IsNormalized W x z) {a : Fin n → ℝ} (ha : a ∈ W) :
    nonposLength x z a ≤ weightedDistance x a z ∧
      weightedDistance x a z ≤ 1 ∧
      weightedDistance x a 0 ≤ posLength x z a + √(1 - nonposLength x z a ^ 2) := by sorry

end FairFacilityLoc
