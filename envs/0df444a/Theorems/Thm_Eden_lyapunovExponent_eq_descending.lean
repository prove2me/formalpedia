-- Prove2me | Theorems.Thm_Eden_lyapunovExponent_eq_descending
-- name    : Eden.lyapunovExponent_eq_descending
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:44:23.541842+00:00
-- url     : https://prove2.me/theorems/1d738861-7bb2-43db-b412-fd10a11a9688
-- title:
--   Eden: lyapunov Exponent eq descending
-- statement:
--   The Eden construction uses the lyapunov Exponent eq descending property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L64-L66
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L64-L66

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.lyapunovExponent_eq_descending (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    lyapunovExponent c p i = descending (factorExponents c p) i := by sorry
