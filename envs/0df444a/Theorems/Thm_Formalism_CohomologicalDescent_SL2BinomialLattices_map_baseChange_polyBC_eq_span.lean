-- Prove2me | Theorems.Thm_Formalism_CohomologicalDescent_SL2BinomialLattices_map_baseChange_polyBC_eq_span
-- name    : Formalism.CohomologicalDescent.SL2BinomialLattices.map_baseChange_polyBC_eq_span
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:59:58.32728+00:00
-- url     : https://prove2.me/theorems/fe996b4a-e2e8-4c89-a3b3-3e41205fb11f
-- title:
--   SL2 Binomial Lattices: map base Change poly BC eq span
-- statement:
--   The SL2 Binomial Lattices construction uses the map base Change poly BC eq span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L311-L328
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PieriBlockIdeals/PieriColumnMinors/SL2BinomialLattices.lean#L311-L328

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

theorem Formalism.CohomologicalDescent.SL2BinomialLattices.map_baseChange_polyBC_eq_span (R O : Type) [CommRing R] [CommRing O] [Algebra R O] (r n : ℕ)
    (q : Submodule R (MvPolynomial (Fin r × Fin n) R)) :
    (q.baseChange O).map (polyBC R O r n).toLinearMap =
      Submodule.span O (map (algebraMap R O) '' (q : Set (MvPolynomial (Fin r × Fin n) R))) := by sorry
