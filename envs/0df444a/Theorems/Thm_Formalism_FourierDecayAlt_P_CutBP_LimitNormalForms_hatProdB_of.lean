-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_CutBP_LimitNormalForms_hatProdB_of
-- name    : Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.hatProdB_of
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T11:27:02.51498+00:00
-- url     : https://prove2.me/theorems/60d50d21-9903-4ca9-be38-22178b7c98f1
-- title:
--   Limit Normal Forms: hat Prod B of
-- statement:
--   The Limit Normal Forms construction uses the hat Prod B of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/HatProd.lean#L287-L292
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/AutomorphicTheory/LocalBesselUniqueness/HatProd.lean#L287-L292

import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_OpLocal
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_BigCellHermitian
import Definitions.Def_CompanionTheory_AutomorphicTheory_LocalBesselUniqueness_HatProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt
set_option linter.unusedSectionVars false
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutBP Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms
open Formalism.FourierDecayAlt.P.CutMP

theorem Formalism.FourierDecayAlt.P.CutBP.LimitNormalForms.hatProdB_of (hA : CapAB) (hR : CapRB) (h0 : JDHatBdd) (h1 : ResidueSplittingModelAlgebra) (h2 : MirrorResidueSplittingModelAlgebra)
    (h3 : JDHatLagrange) (h4 : JDHatNodes) : HatProdB := by sorry
