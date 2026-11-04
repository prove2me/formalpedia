-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_k_rate_uniform_grid_algebra_bridge
-- name    : AvramDividend.Classical.avram_p2_k_rate_uniform_grid_algebra_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T20:05:48.441183+00:00
-- url     : https://prove2.me/theorems/d9573708-0f27-412c-b169-c61e52c1a74b
-- title:
--   A positive small-time rate yields the stationary uniform-mesh expected total
-- statement:
--   For a positive uniform mesh of total real horizon T, any real-valued small-time test expectation with first-order rate L has its stationary (n+1)-cell expected sum converge to T times L. The proof uses only the fixed-total-width identity, nonzero grid widths and composition of Filter.Tendsto; it is the deterministic normalisation bridge between the original Lévy small-time moment-to-test rate and the original stationary uniform-grid expectation theorem. No stochastic intensity is assumed.
-- source:
--   The proved original-source stationary uniform-grid expectation theorem 3c63c970-b4e9-4f60-aae9-0b636f46bb61 together with original-source small-time exponential moment derivative e6973988-8944-43a3-936c-4fe904297c04 reduces final compact test expectation assembly to this exact rate-by-mesh algebra. This statement is a generic finite-product limit and introduces no source-law assumption or alternate process.

import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.NhdsWithin

open Filter Topology Set

theorem AvramDividend.Classical.avram_p2_k_rate_uniform_grid_algebra_bridge
    (δ : ℕ → ℝ) (F : ℝ → ℝ) (T L : ℝ)
    (hδ : Tendsto δ atTop (nhdsWithin (0 : ℝ) (Set.Ioi 0)))
    (hδnz : ∀ n, δ n ≠ 0)
    (hmesh : ∀ n : ℕ, ((n : ℝ) + 1) * δ n = T)
    (hRate : Tendsto (fun h : ℝ => F h / h)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    Tendsto (fun n : ℕ => ((n : ℝ) + 1) * F (δ n))
      atTop (nhds (T * L)) := by sorry
