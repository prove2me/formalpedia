-- Prove2me | Theorems.Thm_EdenVerified_p17_volumeDefect_integrand_nonneg
-- name    : EdenVerified.p17_volumeDefect_integrand_nonneg
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:47:09.810233+00:00
-- url     : https://prove2.me/theorems/b3856a89-c6ae-5577-a323-23cce91dc01a
-- title:
--   Eden Verified: p17 volume Defect integrand nonneg
-- statement:
--   The Eden Verified construction uses the p17 volume Defect integrand nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1534-L1538
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L1534-L1538

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p17_volumeDefect_integrand_nonneg :
    ∀ (c τ : ℝ) (p : PhaseSpace),
    0 ≤ (radiusSq₁ (evolution c τ p) - 1) ^ 2 +
      (radiusSq₂ (evolution c τ p) - 1) ^ 2 := by sorry
