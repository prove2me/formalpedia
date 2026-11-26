-- Prove2me | Theorems.Thm_EdenVerified_periodic_global_growth
-- name    : EdenVerified.periodic_global_growth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T15:25:33.1509+00:00
-- url     : https://prove2.me/theorems/83fdbb8f-17f2-51e2-9af2-7e8fe32b2759
-- title:
--   Eden Verified: periodic global growth
-- statement:
--   Periodic-set spatial suprema before ordinary real-time limits.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L450-L468
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Solution.lean#L450-L468

import Definitions.Def_Eden
import Definitions.Def_Eden_Solution
set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
open EdenVerified

theorem EdenVerified.periodic_global_growth (c : ℝ) (hc : 4 < c) :
    (∀ k : Fin 6, ∀ t : ℝ, 0 ≤ t →
      periodicGlobalLogGrowth c k t = t * (![0, 2, 2, 0, -2, -2 - c] : Fin 6 → ℝ) k) ∧
    (∀ k : Fin 6, Tendsto (fun t : ℝ => periodicGlobalLogGrowth c k t / t)
      atTop (𝓝 ((![0, 2, 2, 0, -2, -2 - c] : Fin 6 → ℝ) k))) ∧
    ((fun k : Fin 6 => periodicGlobalGrowthRate c k) = ![0, 2, 2, 0, -2, -2 - c]) ∧
    (∀ k : ℕ, k < 5 → ∀ α : ℝ, 0 ≤ α → α ≤ 1 →
      periodicGlobalGrowthInterpolation c ((k : ℝ) + α) =
        (1 - α) * periodicGlobalGrowthRate c k + α * periodicGlobalGrowthRate c (k + 1)) := by sorry
