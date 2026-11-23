-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_thGrid_nonneg
-- name    : Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.thGrid_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:20:37.701586+00:00
-- url     : https://prove2.me/theorems/de344211-db57-499a-9811-10aaefa0d9fd
-- title:
--   Polynomial Theorems Assembly: th Grid nonneg
-- statement:
--   The Polynomial Theorems Assembly construction uses the th Grid nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L13-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L13-L16

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_PolynomialTheoremsAssembly
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open scoped ComplexOrder
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly
open Formalism.FourierDecayAlt.PairingProductCorollary

theorem Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.thGrid_nonneg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (j : Fin K → Fin (d + 1)) :
    0 ≤ F7.thGrid grid j := by sorry
