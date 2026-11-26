-- Prove2me | Theorems.Thm_Eden_radiusEvolution_eq_amplitude
-- name    : Eden.radiusEvolution_eq_amplitude
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:26:46.969213+00:00
-- url     : https://prove2.me/theorems/e8669583-e270-4454-85b1-7e2bb07e8abd
-- title:
--   Eden: radius Evolution eq amplitude
-- statement:
--   The Eden construction uses the radius Evolution eq amplitude property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AngularLifts.lean#L16-L25
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/AngularLifts.lean#L16-L25

import Definitions.Def_Eden_PhysicalRadius
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Definitions.Def_Eden_AngularLifts
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.radiusEvolution_eq_amplitude {t r : ℝ} (ht : 0 ≤ t) (hr : 0 ≤ r) :
    radiusEvolution t r = r * planarAmplitude t (r ^ 2) := by sorry
