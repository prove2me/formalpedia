-- Prove2me | Theorems.Thm_EdenVerified_p27_tendstoUniformlyOn_log_singularValueFunction
-- name    : EdenVerified.p27_tendstoUniformlyOn_log_singularValueFunction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:42:13.835523+00:00
-- url     : https://prove2.me/theorems/84a63106-7731-5885-a30b-d1a03b7cd111
-- title:
--   Eden Verified: p27 tendsto Uniformly On log singular Value Function
-- statement:
--   The Eden Verified construction uses the p27 tendsto Uniformly On log singular Value Function property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1184-L1189
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1184-L1189

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p27_tendstoUniformlyOn_log_singularValueFunction :
    ∀ (c : ℝ) (p : PhaseSpace),
    TendstoUniformlyOn (fun t d => Real.log
      (singularValueFunction (fderiv ℝ (evolution c t) p).toLinearMap d) / t)
      (spectrumInterpolation (lyapunovExponent c p)) atTop (Icc 0 5) := by sorry
