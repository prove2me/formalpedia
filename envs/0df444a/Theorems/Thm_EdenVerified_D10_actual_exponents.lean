-- Prove2me | Theorems.Thm_EdenVerified_D10_actual_exponents
-- name    : EdenVerified.D10_actual_exponents
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:26:53.189831+00:00
-- url     : https://prove2.me/theorems/d4245a7f-7d6b-5c63-9123-e81a637792cb
-- title:
--   Eden Verified: D10 actual exponents
-- statement:
--   The spectrum in the convention consists of real-time limits.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L644-L650
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L644-L650

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.D10_actual_exponents (c : ℝ) (p : PhaseSpace) :
    Antitone (lyapunovExponent c p) ∧
    (∀ i : Fin 5, Tendsto (fun t : ℝ => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t)
      atTop (𝓝 (lyapunovExponent c p i))) ∧
    asymptoticDimension c p = kaplanYorkeDimension (lyapunovExponent c p) := by sorry
