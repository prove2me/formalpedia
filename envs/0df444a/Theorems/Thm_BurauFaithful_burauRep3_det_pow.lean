-- Prove2me | Theorems.Thm_BurauFaithful_burauRep3_det_pow
-- name    : BurauFaithful.burauRep3_det_pow
-- status  : Proved
-- author  : @junyihjy
-- created : 2026-09-25T03:18:45.429672+00:00
-- url     : https://prove2.me/theorems/3761b234-60b5-44a6-814d-f58b6543a5db
-- title:
--   Determinant of the degree-3 Burau representation is an integer power of det ρ₃(σ₁)
-- statement:
--   For the unreduced Burau representation ρ₃ of the braid group B₃ over the Laurent polynomial ring ℤ[t,t⁻¹], the determinant of ρ₃(β), as a unit of ℤ[t,t⁻¹], is an integer power of the determinant of ρ₃(σ₁) (which equals the unit -t).

import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BurauFaithful_UnreducedBurau

namespace BurauFaithful

theorem burauRep3_det_pow (β : BraidsLinksMCG.ArtinBraidGroup 3) :
    ∃ k : ℤ, Matrix.GeneralLinearGroup.det (BurauFaithful.burauRep 3 β) =
      (Matrix.GeneralLinearGroup.det (BurauFaithful.burauRep 3
        (BraidsLinksMCG.sigma ⟨0, by decide⟩))) ^ k := by sorry

end BurauFaithful
