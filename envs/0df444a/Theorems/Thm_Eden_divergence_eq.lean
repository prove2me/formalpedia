-- Prove2me | Theorems.Thm_Eden_divergence_eq
-- name    : Eden.divergence_eq
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T14:26:10.225566+00:00
-- url     : https://prove2.me/theorems/23b618f6-a69b-4d67-a78a-93bb69ef0ee5
-- title:
--   Eden: divergence eq
-- statement:
--   The exact global divergence identity holds at every ambient point and
--   for every real parameter.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Divergence.lean#L32-L35
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Divergence.lean#L32-L35

import Definitions.Def_Eden_VectorFieldDerivative
import Definitions.Def_Eden_Divergence
set_option autoImplicit true
noncomputable section
open Eden

theorem Eden.divergence_eq (c : ℝ) (p : PhaseSpace) :
    divergence c p = 4 - c - 6 * (radiusSq₁ p - 1) ^ 2 - 6 * (radiusSq₂ p - 1) ^ 2 := by sorry
