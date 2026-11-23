-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_sq_sum
-- name    : Formalism.FourierDecayAlt.P.DensitySumsAndDomination.sq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:13.03192+00:00
-- url     : https://prove2.me/theorems/2b8c68fc-702c-4af6-bbaa-6f9e624e2f3b
-- title:
--   Density Sums And Domination: sq sum
-- statement:
--   The Density Sums And Domination construction uses the sq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L144-L165
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L144-L165

import Definitions.Def_Formalism_HermitianCurvature_StatementTC
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DensitySumsAndDomination
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology Formalism.FourierDecayAlt Formalism.FourierDecayAlt.TC
open scoped ComplexInnerProductSpace ComplexOrder ComplexConjugate
noncomputable section
open Classical
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DensitySumsAndDomination

theorem Formalism.FourierDecayAlt.P.DensitySumsAndDomination.sq_sum (M : ℕ) : ∑ m ∈ Icc 2 (M + 2), (((m : ℕ) : ℝ) ^ 2)⁻¹ ≤ 3 / 4 - ((M : ℝ) + 2)⁻¹ := by sorry
