-- Prove2me | Theorems.Thm_EdenVerified_p04_isBounded_evolution_image_interval
-- name    : EdenVerified.p04_isBounded_evolution_image_interval
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T15:30:53.929812+00:00
-- url     : https://prove2.me/theorems/e37ede8d-979d-4503-9cd1-4d3ef6625ed0
-- title:
--   Eden Verified: p04 is Bounded evolution image interval
-- statement:
--   The Eden Verified construction uses the p04 is Bounded evolution image interval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L852-L855
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L852-L855

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.p04_isBounded_evolution_image_interval :
    ∀ (c T : ℝ) (p : PhaseSpace),
    Bornology.IsBounded ((fun t => evolution c t p) '' Icc 0 T) := by sorry
