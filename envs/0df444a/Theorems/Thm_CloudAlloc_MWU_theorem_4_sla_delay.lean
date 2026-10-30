-- Prove2me | Theorems.Thm_CloudAlloc_MWU_theorem_4_sla_delay
-- name    : CloudAlloc.MWU.theorem_4_sla_delay
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:46:11.173527+00:00
-- url     : https://prove2.me/theorems/0d34632a-0fd0-4f65-bf8d-b6c57a1ec0f3
-- title:
--   Theorem 4: SLA satisfaction with delay $\tilde p=32\frac{N^2}{\varepsilon^3\eta}\ln(N/\varepsilon)$
-- statement:
--   Let $N\ge 2$, $0<\varepsilon\le 1/10$, $0<\eta\le 1/3$, $\lambda=\varepsilon^2/(8N)$, SLAs with $\beta(j)\ge e^{\eta(1+\lambda)}\varepsilon/N$ for all users and $\sum_j\beta(j)\le 1$, nonnegative loads, $h$ a run of Algorithm 1, and
--
--   $$
--   \tilde p=32\,\frac{N^2}{\varepsilon^3\eta}\ln(N/\varepsilon).
--   $$
--
--   For every user $i$ and every allocation sequence $h'$ with $h'_t(i)=(1-2\varepsilon)\beta(i)$ for all $t$, with $w'$ its work:
--
--   1. for every time $t$, $\displaystyle\sum_{\tau=1}^{t+\tilde p}w_\tau(i)\ \ge\ \sum_{\tau=1}^{t}w'_\tau(i)$;
--   2. for every time $t$, $\displaystyle\sum_{\tau=1}^{t}w_\tau(i)\ \ge\ \sum_{\tau=1}^{t}w'_\tau(i)-\beta(i)\tilde p$.
--
--   The algorithm does for each user, up to a delay $\tilde p$, the work of a static reservation of $(1-2\varepsilon)\beta(i)$; with the SLA comparison it gives clause 2 of Theorem 1.
--
--   Differences from the source:
--   - reading: Σ_{τ=1}^{t+p̃} with real p̃ → sum up to t + ⌊p̃⌋₊; reason: sums range over integer times
--   - encoding: any time t ≤ T − p̃ (first claim) and any t (Moreover) → every t ∈ ℕ; reason: loads and the run are infinite sequences; for each t take T = t + ⌈p̃⌉, and the run up to T does not depend on later loads
--   - generalization: h′_1, …, h′_T allocations with h′_t(i) = (1 − 2ε)β(i) → only coordinate i constrained: h′ τ i = (1 − 2ε)β(i); reason: user i's work under h′ depends only on coordinate i, so the statement specializes to allocations
--   - reading: w_t(i) = min{h_t(i), L_t(i) + Q_t(i)} (p. 3) and the remark "h_t(i) = w_t(i) for all active users" (p. 8) → work is min{h, L + Q}; nothing like w = h for active users is assumed; reason: the p. 3 definition is binding; the p. 8 remark is false when L_t(i) + Q_t(i) < h_t(i)
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Theorem 4, p. 10 (proof p. 13)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run
import Definitions.Def_CloudAlloc_MWU_userWork

namespace CloudAlloc.MWU

/-- **Theorem 4: SLA satisfaction with delay `p̃`.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, Theorem 4, p. 10 (proof p. 13):
"Let `0 < ε ≤ 1/10` and `0 < η ≤ 1/3`. Take any SLAs `β(1), . . . , β(N)` such that
`β(i) ≥ e^{η(1+λ)} ε/N`, where `λ = ε²/(8N)` and let `p̃ = 32 N²/(ε³η) ln(N/ε)`. Then, for any user `i`
and time `t ≤ T − p̃`, if we take `h′1, . . . , h′T` to be allocations such that `h′t(i) = (1 − 2ε) β(i)`,
the work done by Algorithm 1 for user `i` satisfies `Σ_{τ=1}^{t+p̃} wτ(i) ≥ Σ_{τ=1}^t w′τ(i)`, where
`w′t` is the work done by the allocations `h′1, . . . , h′T`. Moreover,
`Σ_{τ=1}^t wτ(i) ≥ Σ_{τ=1}^t w′τ(i) − β(i)p̃`."

For a run of Algorithm 1 with `N ≥ 2`, `0 < ε ≤ 1/10`, `0 < η ≤ 1/3`, SLAs
`β(j) ≥ e^{η(1+λ)}ε/N` with `Σβ ≤ 1` and nonnegative loads, every user `i` and every allocation
sequence `h′` giving user `i` exactly `(1 − 2ε)β(i)` at every step: (1) by time `t + p̃` the algorithm
has done for `i` at least the work `h′` does by time `t`; (2) at every time `t` the algorithm's
cumulative work for `i` is at least that of `h′` minus `β(i)p̃`.

**Formalization Note.** Lean time `τ` is the paper's `τ + 1`. `Σ_{τ=1}^{t+p̃}` runs over the integers
`τ ≤ t + p̃` (real `p̃`), so the Lean limit is `t + ⌊p̃⌋₊`. The run and the loads are infinite sequences,
so the printed `t ≤ T − p̃` (which only keeps `t + p̃` inside the horizon) is covered by every `t`.
Only coordinate `i` of `h′` enters; `h′` has its own queues on the same loads, from `Q_1 = 0`.
`β ≥ 0` is implied by the lower bound on `β` and not stated separately. At `β(j) = e^{η(1+λ)}ε/N`
exactly, the strict `h_t(j) ≤ (ε/N)e^{η(1+λ)} < β(j)` of Lemma 2's proof is an equality; the
statement keeps Theorem 4's printed hypothesis. -/
theorem theorem_4_sla_delay {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η ≤ 1 / 3)
    {β : Fin N → ℝ} (hβ : ∀ j, Real.exp (η * (1 + ε ^ 2 / (8 * (N : ℝ)))) * ε / N ≤ β j)
    (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    let pt := 32 * (N : ℝ) ^ 2 / (ε ^ 3 * η) * Real.log ((N : ℝ) / ε)
    ∀ (i : Fin N) (h' : ℕ → Fin N → ℝ), (∀ τ, h' τ i = (1 - 2 * ε) * β i) →
      (∀ t, userWork h' L i t ≤ userWork h L i (t + ⌊pt⌋₊)) ∧
        (∀ t, userWork h' L i t - β i * pt ≤ userWork h L i t) := by sorry

end CloudAlloc.MWU
