-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_PolynomialTheoremsAssembly_p3aOfParts_ok
-- name    : Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.p3aOfParts_ok
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:31:16.686377+00:00
-- url     : https://prove2.me/theorems/d47d78b4-7c75-47f8-919c-9c0467fefb09
-- title:
--   Polynomial Theorems Assembly: p3a Of Parts ok
-- statement:
--   The Polynomial Theorems Assembly construction uses the p3a Of Parts ok property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L35-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/PolynomialTheoremsAssembly.lean#L35-L128

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

theorem Formalism.FourierDecayAlt.P.PolynomialTheoremsAssembly.p3aOfParts_ok : LeadingBlockRecursiveBoundFromComponents := by sorry
