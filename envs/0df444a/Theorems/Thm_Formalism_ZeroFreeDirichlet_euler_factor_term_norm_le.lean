-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_euler_factor_term_norm_le
-- name    : Formalism.ZeroFreeDirichlet.euler_factor_term_norm_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:37:51.667828+00:00
-- url     : https://prove2.me/theorems/dd608d4b-b1f7-48da-badc-1887d7267a3f
-- title:
--   Zero Free Dirichlet: euler factor term norm le
-- statement:
--   The Zero Free Dirichlet construction uses the euler factor term norm le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean#L55-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/SameCharacterLFunctionOne.lean#L55-L64

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_SameCharacterLFunctionOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet

theorem Formalism.ZeroFreeDirichlet.euler_factor_term_norm_le {M : ℕ} (φ : DirichletCharacter ℂ M) (p : ℕ) :
    ‖φ (p : ZMod M) * (p : ℂ) ^ (-(1 : ℂ))‖ ≤ 1 / (p : ℝ) := by sorry
