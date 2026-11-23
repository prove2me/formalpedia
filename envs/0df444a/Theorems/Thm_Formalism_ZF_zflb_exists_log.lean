-- Prove2me | Theorems.Thm_Formalism_ZF_zflb_exists_log
-- name    : Formalism.ZF.zflb_exists_log
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:36:13.626275+00:00
-- url     : https://prove2.me/theorems/bbe219f6-249e-47cb-898d-c70d860f6066
-- title:
--   ZF: zflb exists log
-- statement:
--   The ZF construction uses the zflb exists log property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivBound.lean#L12-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/LogDerivBound.lean#L12-L40

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Mathlib.Analysis.Complex.BorelCaratheodory
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.Liouville
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_LogDerivBound
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Metric
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.zflb_exists_log {f : ℂ → ℂ} {z₀ : ℂ} {R : ℝ}
    (hf : DifferentiableOn ℂ f (ball z₀ R)) (hne : ∀ z ∈ ball z₀ R, f z ≠ 0) :
    ∃ g : ℂ → ℂ, g z₀ = 0 ∧ (∀ z ∈ ball z₀ R, HasDerivAt g (deriv f z / f z) z) ∧
      ∀ z ∈ ball z₀ R, f z = f z₀ * Complex.exp (g z) := by sorry
