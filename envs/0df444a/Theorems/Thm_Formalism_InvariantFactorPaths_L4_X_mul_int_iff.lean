-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_X_mul_int_iff
-- name    : Formalism.InvariantFactorPaths.L4.X_mul_int_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:34:51.881398+00:00
-- url     : https://prove2.me/theorems/bf76a19c-4568-40d9-8fab-643c367fe1f7
-- title:
--   L4: X mul int iff
-- statement:
--   The L4 construction uses the X mul int iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/InitPartZeroXMul.lean#L71-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/InitPartZeroXMul.lean#L71-L83

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

theorem Formalism.InvariantFactorPaths.L4.X_mul_int_iff (v : σ) (a : MvPolynomial σ ℚ_[p]) : X v * a ∈ IntPol p σ ↔ a ∈ IntPol p σ := by sorry
