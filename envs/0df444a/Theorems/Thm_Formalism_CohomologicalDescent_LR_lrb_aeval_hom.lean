-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_LR_lrb_aeval_hom
-- name    : Formalism.CohomologicalDescent.LR.lrb_aeval_hom
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:48:25.622021+00:00
-- url     : https://prove2.me/theorems/fb2ab80d-29ed-4e37-b55e-199354df5f0d
-- title:
--   LR: lrb aeval hom
-- statement:
--   The LR construction uses the lrb aeval hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L132-L141
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/LrbPiSingleCast.lean#L132-L141

import Definitions.Def_Formalism_GradedWeylDivisibility_FinalD
import Definitions.Def_Formalism_GradedWeylDivisibility_StatementE
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_FockQHW
import Definitions.Def_Formalism_PieriBlockIdeals_StatementLD
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DividedPowerZeroZeroVector
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_LrbPiSingleCast
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.LR
open Formalism.GradedWeylDivisibility
variable (R : Type*) [CommRing R] (p q : ℕ)

theorem Formalism.CohomologicalDescent.LR.lrb_aeval_hom {σ τ Mo : Type*} [AddCommMonoid Mo] (w : τ → Mo) (φ : σ → MvPolynomial τ R) (ω : σ → Mo)
    (hφ : ∀ v, IsWeightedHomogeneous w (φ v) (ω v)) (x : MvPolynomial σ R) (κ : Mo)
    (hx : IsWeightedHomogeneous ω x κ) : IsWeightedHomogeneous w (aeval φ x) κ := by sorry
