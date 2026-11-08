-- Prove2me | Theorems.Thm_FairFacilityLoc_proposition_3_17
-- name    : FairFacilityLoc.proposition_3_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:14:12.972799+00:00
-- url     : https://prove2.me/theorems/5ba7e999-78c7-4e40-a52b-32a2c3f5afbf
-- title:
--   Proposition 3.17 — the weighted capacity is at most $d$
-- statement:
--   For $d\in\{1,2,3\}$, normalized data with $Q_r(a)\le K_r$ for all $a\in W$ and all $r$ satisfy
--   $$\mathcal C\le d,$$
--   and for $d=2$, a coordinate $r^*$ with the largest entry satisfies $K_{r^*}\le2$.
--
--   With Lemma 3.5, Lemma 3.9 and Proposition 3.11 this gives the ratio $1+\sqrt d$.
--
--   Differences from the source:
--   - generalization: normalized coordinates of a mechanism output, where Lemma 3.9 holds → any normalized family with $Q_r(a)\le K_r$ for all $a,r$ (CapacityCondition); reason: the proof uses the mechanism only through this inequality; Lemma 3.9 (`lemma_3_9`) supplies it for a mechanism output
--   - encoding: the normalization (3.2), with the output at the origin → the structure IsNormalized; reason: the fields are the hypotheses (3.2) for a finite nonnegative family with a vector of positive mass
--   - encoding: $d\le 3$ → $1\le d\le 3$; reason: dimensions are positive throughout the paper; (1.2) lists $1\le d\le3$
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Proposition 3.17, p.36 (PDF p.38); family form p.49 (PDF p.51)

import Mathlib
import Definitions.Def_FairFacilityLoc_penalty
import Definitions.Def_FairFacilityLoc_IsNormalized

namespace FairFacilityLoc

/-- **Proposition 3.17** (Yan, Zhou, manuscript, sha256 642a1268…, p.36, PDF p.38). The weighted capacity satisfies
`C ≤ d`. For `d = 2`, the capacity of every coordinate `r*` with the largest entry satisfies `K_{r*} ≤ 2`.

**Formalization Note.** Stated for `d ∈ {1, 2, 3}` and weight families in normalized coordinates, as on p.49;
`CapacityCondition` is the conclusion of Lemma 3.9. -/
theorem proposition_3_17 {n d : ℕ} (hd : 1 ≤ d) (hd3 : d ≤ 3) {W : Finset (Fin n → ℝ)}
    {x : Fin n → GeoSemialgCSP.E d} {z : GeoSemialgCSP.E d} (hN : IsNormalized W x z)
    (hC : CapacityCondition (penalty d) W x) :
    weightedCapacity (penalty d) W x z ≤ (d : ℝ) ∧
      (d = 2 → ∀ rs, IsTopCoord z rs → capacity (penalty d) W x rs ≤ 2) := by sorry

end FairFacilityLoc
