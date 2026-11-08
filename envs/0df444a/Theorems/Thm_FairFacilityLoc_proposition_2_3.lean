-- Prove2me | Theorems.Thm_FairFacilityLoc_proposition_2_3
-- name    : FairFacilityLoc.proposition_2_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T11:11:23.434469+00:00
-- url     : https://prove2.me/theorems/5027f78b-f23b-45ea-ae87-2eee377764f6
-- title:
--   Proposition 2.3 — sublinear effects are exactly the effects with a weight set
-- statement:
--   Let $E$ be a group effect of a group $G$.
--
--   1. If $E$ is sublinear, then $K(E)=\{a\in\mathbb R^G_{\ge0}:\sum_ia_iu_i\le E(u)\text{ for all }u\in\mathbb R^G_{\ge0}\}$ is a weight set of $E$.
--   2. The group effect $E$ is sublinear if and only if it has a weight set.
--
--   This is the formulation of sublinear effects that the mechanism uses: every sublinear effect is a maximum of weighted total distances.
--
--   Differences from the source: none.
-- source:
--   Yan, Zhou, Fair and Strategyproof Facility Location in Euclidean Space, manuscript (sha256 642a1268…), Proposition 2.3, p.14 (PDF p.16)

import Mathlib
import Definitions.Def_FairFacilityLoc_IsGroupEffect
import Definitions.Def_FairFacilityLoc_IsSublinearEffect
import Definitions.Def_FairFacilityLoc_IsWeightSet
import Definitions.Def_FairFacilityLoc_canonicalWeightSet

open scoped NNReal

namespace FairFacilityLoc

/-- **Proposition 2.3** (Yan, Zhou, *Fair and Strategyproof Facility Location in Euclidean Space*, manuscript,
sha256 642a1268…, p.14, PDF p.16). Let `E` be a group effect of a group `G`. (a) If `E` is sublinear, then `K(E)` is a
weight set of `E`. (b) `E` is sublinear if and only if it has a weight set. -/
theorem proposition_2_3 {n : ℕ} (G : Finset (Fin n)) (hG : G.Nonempty) (E : (↥G → ℝ≥0) → ℝ≥0)
    (hE : IsGroupEffect E) :
    (IsSublinearEffect E → IsWeightSet E (canonicalWeightSet E)) ∧
      (IsSublinearEffect E ↔ ∃ K, IsWeightSet E K) := by sorry

end FairFacilityLoc
