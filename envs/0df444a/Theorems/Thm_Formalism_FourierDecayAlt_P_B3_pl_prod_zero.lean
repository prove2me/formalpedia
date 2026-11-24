-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_B3_pl_prod_zero
-- name    : Formalism.FourierDecayAlt.P.B3.pl_prod_zero
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:33:09.829549+00:00
-- url     : https://prove2.me/theorems/de5b837f-0e2c-4a4a-82c2-24ab9d6ab313
-- title:
--   B3: pl prod zero
-- statement:
--   The B3 construction uses the pl prod zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L70-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AeEqualityFromTestFunctions.lean#L70-L75

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.B3
open Formalism.FourierDecayAlt.B

theorem Formalism.FourierDecayAlt.P.B3.pl_prod_zero {a₁ b₁ a₂ b₂ k : ℝ} (hk : 0 ≤ k) {τ : ℝ × ℝ} (hτ : τ ∉ Ioo a₁ b₁ ×ˢ Ioo a₂ b₂) :
    pl a₁ b₁ k τ.1 * pl a₂ b₂ k τ.2 = 0 := by sorry
