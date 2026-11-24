-- Prove2me | Theorems.Thm_Formalism_ZF_riemannZeta_ne_zero_of_mem_rectangle
-- name    : Formalism.ZF.riemannZeta_ne_zero_of_mem_rectangle
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:41:27.304799+00:00
-- url     : https://prove2.me/theorems/95e3e32a-75a9-41da-a4e0-199bd0afbdfe
-- title:
--   ZF: riemann Zeta ne zero of mem rectangle
-- statement:
--   The ZF construction uses the riemann Zeta ne zero of mem rectangle property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RiemannZetaNeZeroOfMemRectangle.lean#L27-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZeroFreeRegion/ZetaLogDerivativeBounds/RiemannZetaNeZeroOfMemRectangle.lean#L27-L33

import Definitions.Def_Formalism_ZeroFreeRegion_SmallHeightLogDeriv
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaNeZeroOfMemRectangle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory
noncomputable section
open Formalism Formalism.ZF

theorem Formalism.ZF.riemannZeta_ne_zero_of_mem_rectangle (c₀ : ℝ)
    (hZ : ∀ s : ℂ, s ≠ 1 → 1 - c₀ / Real.log (|s.im| + 2) ≤ s.re → riemannZeta s ≠ 0)
    (c T σ₀ : ℝ) (hc : 0 < c) (hcc : c ≤ c₀) (hT : 0 ≤ T) :
    ∀ w : ℂ, 1 - c / Real.log (T + 2) ≤ w.re → w.re ≤ σ₀ → |w.im| ≤ T → w ≠ 1 →
      riemannZeta w ≠ 0 := by sorry
