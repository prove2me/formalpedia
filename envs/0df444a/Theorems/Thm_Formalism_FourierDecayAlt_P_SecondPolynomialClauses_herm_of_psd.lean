-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_herm_of_psd
-- name    : Formalism.FourierDecayAlt.P.SecondPolynomialClauses.herm_of_psd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:26:29.547645+00:00
-- url     : https://prove2.me/theorems/4f43d59e-9b48-4d21-9bc1-358deb83ea7a
-- title:
--   Second Polynomial Clauses: herm of psd
-- statement:
--   The Second Polynomial Clauses construction uses the herm of psd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L68-L80
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L68-L80

import Definitions.Def_Formalism_HermitianCurvature_LowerBlockNormalisedBoundFromComponents
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SecondPolynomialClauses
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.SecondPolynomialClauses
open Formalism.FourierDecayAlt.PairingProductCorollary

theorem Formalism.FourierDecayAlt.P.SecondPolynomialClauses.herm_of_psd {V : Type} [AddCommGroup V] [Module ℂ V] (R : Formalism.FourierDecayAlt.F7.Sesq V) (hR : PSD R)
    (x y : V) : (starRingEnd ℂ) (R x y) = R y x := by sorry
