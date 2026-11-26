-- Prove2me | Theorems.Thm_Eden_divergence_eq_rates
-- name    : Eden.divergence_eq_rates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:20:28.149317+00:00
-- url     : https://prove2.me/theorems/9400b525-aa7e-5b97-a83a-22680ca2491b
-- title:
--   Eden: divergence eq rates
-- statement:
--   The Eden construction uses the divergence eq rates property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Divergence.lean#L19-L28
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Divergence.lean#L19-L28

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_Divergence
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.divergence_eq_rates (c : ℝ) (p : PhaseSpace) :
    divergence c p = radialRate (radiusSq₁ p) + tangentialRate (radiusSq₁ p) +
      radialRate (radiusSq₂ p) + tangentialRate (radiusSq₂ p) - c := by sorry
