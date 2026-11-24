-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_polyBC_tmul
-- name    : Formalism.CohomologicalDescent.SL2BinomialLattices.polyBC_tmul
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:58:52.562221+00:00
-- url     : https://prove2.me/theorems/c8f41ac6-1839-48fd-95b8-8239061dab35
-- title:
--   SL2 Binomial Lattices: poly BC tmul
-- statement:
--   The SL2 Binomial Lattices construction uses the poly BC tmul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L306-L309
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L306-L309

import Definitions.Def_Formalism_PieriBlockIdeals_ExponentBoundCounterexample
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_CountLeftInvSeqAlternatingWordEven
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_MaxValEqZeroOfLt
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_SL2BinomialLattices
import Theorems.Thm_Formalism_GradedWeylDivisibility_CoeffHom_algebraMap

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MvPolynomial CategoryTheory TensorProduct
noncomputable section
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.SL2BinomialLattices
open Formalism.GradedWeylDivisibility Formalism.RankGapBounds.JumpSetsAlt Formalism.CohomologicalDescent.LA
universe u v u' v'

theorem Formalism.CohomologicalDescent.SL2BinomialLattices.polyBC_tmul (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (r n : ℕ) (a : O)
    (f : MvPolynomial (Fin r × Fin n) R) :
    polyBC R O r n (a ⊗ₜ[R] f) = a • map (algebraMap R O) f := by sorry
