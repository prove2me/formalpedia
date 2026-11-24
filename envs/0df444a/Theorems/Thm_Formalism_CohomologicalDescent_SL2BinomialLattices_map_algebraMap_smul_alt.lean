-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_map_algebraMap_smul_alt
-- name    : Formalism.CohomologicalDescent.SL2BinomialLattices.map_algebraMap_smul_alt
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T23:00:04.077771+00:00
-- url     : https://prove2.me/theorems/7f112ecb-d8bf-4491-95bc-f349e710195c
-- title:
--   SL2 Binomial Lattices: map algebra Map smul alt
-- statement:
--   The SL2 Binomial Lattices construction uses the map algebra Map smul alt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L330-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L330-L333

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

theorem Formalism.CohomologicalDescent.SL2BinomialLattices.map_algebraMap_smul_alt (R O : Type) [CommRing R] [CommRing O] [Algebra R O] {σ : Type} (a : R)
    (f : MvPolynomial σ R) :
    map (algebraMap R O) (a • f) = algebraMap R O a • map (algebraMap R O) f := by sorry
