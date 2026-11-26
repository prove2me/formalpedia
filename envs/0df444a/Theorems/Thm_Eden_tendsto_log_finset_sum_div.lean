-- Prove2me | Theorems.Thm_Eden_tendsto_log_finset_sum_div
-- name    : Eden.tendsto_log_finset_sum_div
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T13:27:32.598065+00:00
-- url     : https://prove2.me/theorems/5823c0a7-e426-4e05-879e-36e9628404cb
-- title:
--   Eden: tendsto log finset sum div
-- statement:
--   Every nonempty finite positive sum has the maximal individual
--   logarithmic growth rate, along all real times tending to infinity.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicSums.lean#L52-L74
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/LogarithmicSums.lean#L52-L74

import Definitions.Def_Eden_RealTimeAverages
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Definitions.Def_Eden_LogarithmicSums
set_option autoImplicit true
noncomputable section
open Filter Set
open scoped Topology
open Eden

theorem Eden.tendsto_log_finset_sum_div {I : Type*} (s : Finset I) (hs : s.Nonempty)
    (f : I → ℝ → ℝ) (a : I → ℝ)
    (hfpos : ∀ i ∈ s, ∀ᶠ t in atTop, 0 < f i t)
    (hf : ∀ i ∈ s, Tendsto (fun t => Real.log (f i t) / t) atTop (𝓝 (a i))) :
    Tendsto (fun t => Real.log (∑ i ∈ s, f i t) / t) atTop (𝓝 (s.sup' hs a)) := by sorry
