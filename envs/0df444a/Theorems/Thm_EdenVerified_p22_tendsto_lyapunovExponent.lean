-- Prove2me | Theorems.Thm_EdenVerified_p22_tendsto_lyapunovExponent
-- name    : EdenVerified.p22_tendsto_lyapunovExponent
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:49:37.025784+00:00
-- url     : https://prove2.me/theorems/a2ba8fd3-d366-58d3-b779-c8fb186a9e54
-- title:
--   Eden Verified: p22 tendsto lyapunov Exponent
-- statement:
--   The Eden Verified construction uses the p22 tendsto lyapunov Exponent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1693-L1698
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1693-L1698

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p22_tendsto_lyapunovExponent :
    ∀ (c : ℝ) (p : PhaseSpace) (i : Fin 5),
    Tendsto (fun t => Real.log
      ((fderiv ℝ (evolution c t) p).toLinearMap.singularValues i) / t) atTop
      (𝓝 (lyapunovExponent c p i)) := by sorry
