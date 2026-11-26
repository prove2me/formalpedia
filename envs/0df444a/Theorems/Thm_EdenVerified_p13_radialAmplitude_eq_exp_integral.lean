-- Prove2me | Theorems.Thm_EdenVerified_p13_radialAmplitude_eq_exp_integral
-- name    : EdenVerified.p13_radialAmplitude_eq_exp_integral
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:45:08.792457+00:00
-- url     : https://prove2.me/theorems/ba726cce-e058-53ca-86b6-5fbb6ee7632d
-- title:
--   Eden Verified: p13 radial Amplitude eq exp integral
-- statement:
--   The Eden Verified construction uses the p13 radial Amplitude eq exp integral property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1450-L1454
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1450-L1454

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p13_radialAmplitude_eq_exp_integral :
    ∀ {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s),
    radialAmplitude t s =
      Real.exp (∫ τ in (0 : ℝ)..t, radialRate (squaredRadiusEvolution τ s)) := by sorry
