-- Prove2me | Theorems.Thm_EdenVerified_p13_log_planarAmplitude_eq_integral
-- name    : EdenVerified.p13_log_planarAmplitude_eq_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:46:26.593397+00:00
-- url     : https://prove2.me/theorems/a7913554-cdb1-472c-a135-c32b823f267b
-- title:
--   Eden Verified: p13 log planar Amplitude eq integral
-- statement:
--   The Eden Verified construction uses the p13 log planar Amplitude eq integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1432-L1436
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1432-L1436

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p13_log_planarAmplitude_eq_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    Real.log (planarAmplitude t s) =
      ∫ τ in (0 : ℝ)..t, tangentialRate (squaredRadiusEvolution τ s) := by sorry
