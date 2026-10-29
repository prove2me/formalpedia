-- Prove2me | Theorems.Thm_BramsonQueueing_Instability_workload_decrease
-- name    : BramsonQueueing.Instability.workload_decrease
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-29T02:20:53.711579+00:00
-- url     : https://prove2.me/theorems/32025826-35e0-4eb9-a925-31d2575cc260
-- title:
--   Equation (3.5) — immediate workload decrease as printed
-- statement:
--   Consider the random Lu–Kumar network with arbitrary positive service means and any finite initial queue vector. Write $Z_k(t)$ for its class counts and $W_j(t)$ for its immediate station workload. The printed assertion is that, almost surely, for every $0\le t_1\le t_2$,
--   $$\bigl[Z_2(t)>0\text{ and }Z_4(t)>0\text{ for all }t\in(t_1,t_2]\bigr]\ \Longrightarrow\ W_2(t_2)=W_2(t_1)-(t_2-t_1).$$
--   This is the workload observation used in the source before its discussion of the first empty high-priority queue. The equation is retained as printed. Under the book's explicit immediate-workload convention (4.44), internal routing from class 2 to class 3 adds work at station 2; the resulting source counterexample is recorded separately in INSIGHTS.yaml, without changing this target.
--
--   Differences from the source:
--   - encoding: classes 1–4 and stations 1–2 → Fin 4 and Fin 2, indexed from zero; reason: subtracting one from each label preserves all routes, means, and priority comparisons
--   - encoding: the random network on its probability space → an arbitrary probability space carrying the specified primitives and its queue-conserving service-clock trajectories; reason: this is a realization of the source process, with no restriction on its law or queue lengths
-- source:
--   Maury Bramson, Stability of Queueing Networks, LNM 1950, Springer (2008), DOI 10.1007/978-3-540-68896-9, Equation (3.5), antecedent (3.4), printed 57 / PDF 65

import Mathlib
import Definitions.Def_BramsonQueueing_Instability_LuKumarRun

namespace BramsonQueueing.Instability

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal

/-- Equation (3.5), with antecedent (3.4), as printed. -/
theorem workload_decrease {Ω : Type*} [MeasureSpace Ω] [IsProbabilityMeasure (volume : Measure Ω)]
    {d : LuKumarParameters} {p : LuKumarPrimitives Ω d}
    {z₀ : Fin 4 → ℕ} (r : LuKumarRun p z₀) :
    ∀ᵐ ω, ∀ t₁ t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ →
      (∀ t ∈ Set.Ioc t₁ t₂, 0 < r.Z t ω 1 ∧ 0 < r.Z t ω 3) →
      workload r 1 t₂ ω = workload r 1 t₁ ω - (t₂ - t₁) := by sorry

end BramsonQueueing.Instability
