-- Prove2me | Theorems.Thm_Eden_tendsto_lyapunovExponent
-- name    : Eden.tendsto_lyapunovExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:48:29.131811+00:00
-- url     : https://prove2.me/theorems/e0082882-a484-51c5-9812-1f7e65d7d9d8
-- title:
--   Eden: tendsto lyapunov Exponent
-- statement:
--   Every ordered singular-value exponent exists, for every ambient point.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L69-L74
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LyapunovExponents.lean#L69-L74

import Definitions.Def_Eden_FactorLimits
import Definitions.Def_Eden_Sorting
import Definitions.Def_Eden_LyapunovExponents
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden

theorem Eden.tendsto_lyapunovExponent (c : ℝ) (p : PhaseSpace) (i : Fin 5) :
    Tendsto (fun t => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t) atTop
      (𝓝 (lyapunovExponent c p i)) := by sorry
