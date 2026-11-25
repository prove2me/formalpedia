-- Prove2me | Theorems.Thm_Formalism_InvariantFactorPaths_G7_exists_isometric_ext_root
-- name    : Formalism.InvariantFactorPaths.G7.exists_isometric_ext_root
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T02:24:54.574004+00:00
-- url     : https://prove2.me/theorems/8af21813-5a35-5629-9622-75221ec0c7c0
-- title:
--   G7: exists isometric ext root
-- statement:
--   The G7 construction uses the exists isometric ext root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WChain.lean#L12-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ThetaLogCoordinates/UniformThetaSubstitution/FrobeniusLiftNorms/WChain.lean#L12-L33

import Mathlib
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_StatementGK
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_KernelFromKOne
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WModel
import Definitions.Def_Formalism_ThetaLogCoordinates_UniformThetaSubstitution_FrobeniusLiftNorms_WChain
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.G7

theorem Formalism.InvariantFactorPaths.G7.exists_isometric_ext_root (K0 : Type) [i0 : NormedField K0] [IsUltrametricDist K0]
    [CharZero K0] [CompleteSpace K0] (p : ℕ) (hp : p.Prime) (hn : ‖(p : K0)‖ = (p : ℝ)⁻¹) :
    ∃ (K : Type) (_ : NormedField K) (_ : IsUltrametricDist K) (_ : CharZero K) (j : K0 →+* K)
      (ϖ : K), (∀ a, ‖j a‖ = ‖a‖) ∧ ϖ ^ (p ^ 2 - 1) = (p : K) := by sorry
