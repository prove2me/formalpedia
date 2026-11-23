-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_SecondPolynomialClauses_cg_pos
-- name    : Formalism.FourierDecayAlt.P.SecondPolynomialClauses.cg_pos
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T02:28:28.505003+00:00
-- url     : https://prove2.me/theorems/a9ee6b4e-74ed-45f0-9b54-ea9a78cf9890
-- title:
--   Second Polynomial Clauses: cg pos
-- statement:
--   The Second Polynomial Clauses construction uses the cg pos property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L198-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SecondPolynomialClauses.lean#L198-L202

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

theorem Formalism.FourierDecayAlt.P.SecondPolynomialClauses.cg_pos {K d : ℕ} (grid : Fin K → Fin (d + 1) → ℝ) (hg : ∀ a, Function.Injective (grid a)) (a : Fin K) :
    0 < cg grid a := by sorry
