-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_sum_abs_coProd
-- name    : Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.sum_abs_coProd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:31:49.550726+00:00
-- url     : https://prove2.me/theorems/2d6757a5-d9cf-4419-a5c3-6789651bb27e
-- title:
--   Polynomial Theorems Assembly: sum abs co Prod
-- statement:
--   The Polynomial Theorems Assembly construction uses the sum abs co Prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L18-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L18-L21

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

theorem Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.sum_abs_coProd {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) :
    ∑ j, |coProd grid j| = ∏ a, cg grid a := by sorry
