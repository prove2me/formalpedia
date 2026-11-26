-- Prove2me | Theorems.Thm_Eden_lyapunovExponent_bounds
-- name    : Eden.lyapunovExponent_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:34.403264+00:00
-- url     : https://prove2.me/theorems/fe230044-359a-4d45-b89b-57970e2ae7a8
-- title:
--   Eden: lyapunov Exponent bounds
-- statement:
--   The Eden construction uses the lyapunov Exponent bounds property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L15-L28
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L15-L28

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.lyapunovExponent_bounds {c : ℝ} (hc : 4 < c) (p : PhaseSpace)
    (i : Fin 5) : -c ≤ lyapunovExponent c p i ∧ lyapunovExponent c p i ≤ 2 := by sorry
