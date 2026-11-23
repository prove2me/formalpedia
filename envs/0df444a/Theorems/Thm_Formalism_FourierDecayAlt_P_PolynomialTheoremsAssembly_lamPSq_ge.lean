-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_lamPSq_ge
-- name    : Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.lamPSq_ge
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:31:09.11186+00:00
-- url     : https://prove2.me/theorems/a104d4f6-4692-468f-878d-b7da4cf8568b
-- title:
--   Polynomial Theorems Assembly: lam PSq ge
-- statement:
--   The Polynomial Theorems Assembly construction uses the lam PSq ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L23-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L23-L27

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

theorem Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.lamPSq_ge {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (Rw ZZ : ℝ) (a : Fin K) :
    cg grid a ^ 2 * Rw * ZZ ≤ lamPSq grid Rw ZZ := by sorry
