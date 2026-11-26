-- Prove2me | Theorems.Thm_EdenVerified_p10_radialAmplitude_eq_exp_integral
-- name    : EdenVerified.p10_radialAmplitude_eq_exp_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:33:23.066794+00:00
-- url     : https://prove2.me/theorems/10dbbbf2-eca8-53ab-97c9-05ae150a4aef
-- title:
--   Eden Verified: p10 radial Amplitude eq exp integral
-- statement:
--   The Eden Verified construction uses the p10 radial Amplitude eq exp integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1013-L1017
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1013-L1017

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p10_radialAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) := by sorry
