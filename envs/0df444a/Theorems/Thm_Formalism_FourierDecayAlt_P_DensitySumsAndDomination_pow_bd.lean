-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_DensitySumsAndDomination_pow_bd
-- name    : Formalism.FourierDecayAlt.P.DensitySumsAndDomination.pow_bd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:02:08.62138+00:00
-- url     : https://prove2.me/theorems/b785b9b9-e675-4b53-9166-e123979d6910
-- title:
--   Density Sums And Domination: pow bd
-- statement:
--   The Density Sums And Domination construction uses the pow bd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L167-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/DensitySumsAndDomination.lean#L167-L180

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

theorem Formalism.FourierDecayAlt.P.DensitySumsAndDomination.pow_bd (m n : ℕ) (hm : 2 ≤ m) (hn : 2 ≤ n) :
    (((m : ℕ) : ℝ) ^ n)⁻¹ ≤ 4 * ((2 : ℝ) ^ n)⁻¹ * (((m : ℕ) : ℝ) ^ 2)⁻¹ := by sorry
