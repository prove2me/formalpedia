-- Prove2me | Theorems.Thm_Eden_lyapunovExponent_fifth
-- name    : Eden.lyapunovExponent_fifth
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:02:41.423158+00:00
-- url     : https://prove2.me/theorems/63172ca8-e36f-48a5-ae1d-b27643c34e4b
-- title:
--   Eden: lyapunov Exponent fifth
-- statement:
--   The Eden construction uses the lyapunov Exponent fifth property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L30-L42
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/ExponentSums.lean#L30-L42

import Definitions.Def_Eden_DimensionTable
import Definitions.Def_Eden_ExponentSums
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.lyapunovExponent_fifth {c : ℝ} (hc : 4 < c) (p : PhaseSpace) :
    lyapunovExponent c p 4 = -c := by sorry
