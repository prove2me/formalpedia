-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_initPart_smul
-- name    : Formalism.InvariantFactorPaths.L4.initPart_smul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:26:25.459407+00:00
-- url     : https://prove2.me/theorems/b14c5d21-78c2-4f46-9437-7575403e91e0
-- title:
--   L4: init Part smul
-- statement:
--   The L4 construction uses the init Part smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/InitPartZeroXMul.lean#L47-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/InitPartZeroXMul.lean#L47-L51

import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_ShiftLastLetterThresholds
import Definitions.Def_Formalism_PolynomialDimension_MultinomialDepth_PartnerM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam
import Definitions.Def_Formalism_ThetaLogCoordinates_FockResolutionOnto_FockMonomialProofs_InitPartZeroXMul
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.L4
open Formalism.GM Formalism.GM.M Formalism.GM.TM Formalism.GM.MeanGammaLemmas Formalism.CountingSumsFrames MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {σ : Type}

theorem Formalism.InvariantFactorPaths.L4.initPart_smul (v : σ) (e : ℕ) (c : ℚ_[p]) (f : MvPolynomial σ ℚ_[p]) :
    initPart v e (c • f) = c • initPart v e f := by sorry
