-- Prove2me | Theorems.Thm_Formalism_ZeroFreeDirichlet_exponential_integral_nonneg_real
-- name    : Formalism.ZeroFreeDirichlet.exponential_integral_nonneg_real
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T10:42:39.808908+00:00
-- url     : https://prove2.me/theorems/60fc1f7f-4314-4ba6-ae6c-f3f76f548812
-- title:
--   Zero Free Dirichlet: exponential integral nonneg real
-- statement:
--   The Zero Free Dirichlet construction uses the exponential integral nonneg real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZetaNegReal.lean#L10-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LandauZeroFreeBounds/ExceptionalZeroBounds/ZetaNegReal.lean#L10-L27

import Definitions.Def_Formalism_LandauZeroFreeBounds_SameCharacterLFunctionOne
import Definitions.Def_Formalism_ZeroFreeRegion_ZetaLogDerivativeBounds_RiemannZetaOneEqOneSubOfRePos
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaNegReal
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

theorem Formalism.ZeroFreeDirichlet.exponential_integral_nonneg_real {σ a : ℝ} (hσ : 0 ≤ σ) (ha : 0 < a) :
    ∃ r : ℝ, 0 ≤ r ∧ Formalism.ZF.ComplexPowerDifferenceIntegral.eint (σ : ℂ) a = (r : ℂ) := by sorry
