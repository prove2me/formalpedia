-- Prove2me | Theorems.Thm_Eden_lyapunovExponent_antitone
-- name    : Eden.lyapunovExponent_antitone
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:53:17.747012+00:00
-- url     : https://prove2.me/theorems/6c67243c-f0a7-47b3-848c-59570f8524df
-- title:
--   Eden: lyapunov Exponent antitone
-- statement:
--   The Eden construction uses the lyapunov Exponent antitone property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L76-L80
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L76-L80

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.lyapunovExponent_antitone (c : ℝ) (p : PhaseSpace) :
    Antitone (lyapunovExponent c p) := by sorry
