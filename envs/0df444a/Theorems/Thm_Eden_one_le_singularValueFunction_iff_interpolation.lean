-- Prove2me | Theorems.Thm_Eden_one_le_singularValueFunction_iff_interpolation
-- name    : Eden.one_le_singularValueFunction_iff_interpolation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:13.399825+00:00
-- url     : https://prove2.me/theorems/061c99f1-3eb7-41c4-a3a0-462117d77fce
-- title:
--   Eden: one le singular Value Function iff interpolation
-- statement:
--   The Eden construction uses the one le singular Value Function iff interpolation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeKaplanYorke.lean#L23-L28
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeKaplanYorke.lean#L23-L28

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_FiniteTimeKaplanYorke
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.one_le_singularValueFunction_iff_interpolation (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) (d : ℝ) :
    1 ≤ singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d ↔
      0 ≤ spectrumInterpolation (normalizedLogSingularValues c t p) d := by sorry
