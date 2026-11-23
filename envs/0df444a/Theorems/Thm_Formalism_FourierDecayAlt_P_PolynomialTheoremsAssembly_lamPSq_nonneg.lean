-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_lamPSq_nonneg
-- name    : Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.lamPSq_nonneg
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:31:11.927623+00:00
-- url     : https://prove2.me/theorems/00f06061-0e6d-4fa9-8471-56fa6b679e79
-- title:
--   Polynomial Theorems Assembly: lam PSq nonneg
-- statement:
--   The Polynomial Theorems Assembly construction uses the lam PSq nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L29-L33

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

theorem Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.lamPSq_nonneg {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (Rw ZZ : ℝ) :
    0 ≤ lamPSq grid Rw ZZ := by sorry
