-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_L4_intPol_iff_norm
-- name    : Formalism.InvariantFactorPaths.L4.intPol_iff_norm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:25:48.990905+00:00
-- url     : https://prove2.me/theorems/c13b69ee-6c1f-4770-a5ac-9d86f0d9af7a
-- title:
--   L4: int Pol iff norm
-- statement:
--   The L4 construction uses the int Pol iff norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/InitPartZeroXMul.lean#L11-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/FockResolutionOnto/FockMonomialProofs/InitPartZeroXMul.lean#L11-L27

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

theorem Formalism.InvariantFactorPaths.L4.intPol_iff_norm (x : MvPolynomial σ ℚ_[p]) : x ∈ IntPol p σ ↔ ∀ m, ‖x.coeff m‖ ≤ 1 := by sorry
