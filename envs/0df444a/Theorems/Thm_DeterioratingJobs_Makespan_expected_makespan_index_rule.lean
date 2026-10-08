-- Prove2me | Theorems.Thm_DeterioratingJobs_Makespan_expected_makespan_index_rule
-- name    : DeterioratingJobs.Makespan.expected_makespan_index_rule
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T02:08:23.18212+00:00
-- url     : https://prove2.me/theorems/e4dcbf5a-f8aa-447a-967f-0166351fd0bf
-- title:
--   Section 1 — under linear deterioration, sequencing by increasing $\mathrm E(X_i)/\alpha_i$ minimizes the expected makespan
-- statement:
--   Consider $N$ jobs on a single processor, all available at time $0$. Job $i$ has a random initial processing requirement $X_i$ on a probability space $(\Omega,\mathcal F,P)$, assumed integrable, and a growth rate $\alpha_i>0$: if it is started at time $t$, its actual processing time is $X_i+\alpha_i t$. A schedule is a permutation $\pi$ ($\pi(i)=j$: job $j$ is processed $i$-th), processed without preemption or idling, with makespan $S_N(\pi)$.
--
--   If $\pi$ schedules the jobs by increasing values of the index $\mathrm E(X_i)/\alpha_i$, the ratio of expected initial processing requirement to growth rate, i.e.
--
--   $$
--   \frac{\mathrm E(X_{\pi(1)})}{\alpha_{\pi(1)}} \le \frac{\mathrm E(X_{\pi(2)})}{\alpha_{\pi(2)}} \le \dots \le \frac{\mathrm E(X_{\pi(N)})}{\alpha_{\pi(N)}},
--   $$
--
--   then $\pi$ minimizes the expected makespan:
--
--   $$
--   \mathrm E\, S_N(\pi) \le \mathrm E\, S_N(\sigma) \quad\text{for every permutation } \sigma.
--   $$
--
--   Without deterioration the expected makespan is the same for every non-idling schedule; with job-specific linear deterioration it depends on the order, and this index rule identifies an optimal order.
--
--   **Formalization Note** "Minimized when the jobs are scheduled by increasing values" is read as: every permutation along which the index is non-strictly increasing (any tie-break) achieves the minimum over all permutations. The paper's $\alpha_i>0$ is implicit (it divides by $\alpha_i$) and is a hypothesis here. Integrability of each $X_i$ is assumed so that the expectations are meaningful. The paper's positivity of $X_i$ and the usual independence of the $X_i$ are not assumed; the statement holds without them, which makes it slightly more general than the paper's. Jobs and positions are 0-based.
-- source:
--   Browne, Yechiali, Scheduling Deteriorating Jobs on a Single Processor, Oper. Res. 38 (1990), p. 496, Section 1, the sentence after Eq. (2)

import Mathlib
import Definitions.Def_DeterioratingJobs_Makespan_Model

namespace DeterioratingJobs.Makespan

open MeasureTheory

/-- Browne–Yechiali 1990, p. 496, Section 1, the sentence after Eq. (2): with growth rates
`α_i > 0`, any schedule `π` that processes the jobs by increasing `E(X_i)/α_i` minimizes the
expected makespan `E S_N` over all schedules. -/
theorem expected_makespan_index_rule {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {N : ℕ} (X : Fin N → Ω → ℝ) (hX : ∀ i, Integrable (X i) P)
    (α : Fin N → ℝ) (hα : ∀ i, 0 < α i) (π : Equiv.Perm (Fin N))
    (hπ : Monotone (fun k : Fin N => (∫ ω, X (π k) ω ∂P) / α (π k))) :
    ∀ σ : Equiv.Perm (Fin N), expectedMakespan P X α π ≤ expectedMakespan P X α σ := by sorry

end DeterioratingJobs.Makespan
