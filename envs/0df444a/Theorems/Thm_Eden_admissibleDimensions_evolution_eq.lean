-- Prove2me | Theorems.Thm_Eden_admissibleDimensions_evolution_eq
-- name    : Eden.admissibleDimensions_evolution_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:57:06.509899+00:00
-- url     : https://prove2.me/theorems/8f3f71d1-de8b-5efe-956e-95bf005632a5
-- title:
--   Eden: admissible Dimensions evolution eq
-- statement:
--   The Eden construction uses the admissible Dimensions evolution eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeKaplanYorke.lean#L30-L45
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/FiniteTimeKaplanYorke.lean#L30-L45

import Definitions.Def_Eden_InterpolationSign
import Definitions.Def_Eden_FiniteTimeKaplanYorke
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.admissibleDimensions_evolution_eq (c : ℝ) {t : ℝ} (ht : 0 < t)
    (p : PhaseSpace) :
    admissibleDimensions (fderiv ℝ (evolution c t) p).toLinearMap =
      Icc 0 (kaplanYorkeDimension (normalizedLogSingularValues c t p)) := by sorry
