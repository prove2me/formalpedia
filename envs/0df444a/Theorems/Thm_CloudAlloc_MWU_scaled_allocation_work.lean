-- Prove2me | Theorems.Thm_CloudAlloc_MWU_scaled_allocation_work
-- name    : CloudAlloc.MWU.scaled_allocation_work
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:43:33.766659+00:00
-- url     : https://prove2.me/theorems/f47fe6d0-6e51-4afc-8c31-ac4102d4ee65
-- title:
--   Proof of Theorem 1: scaled allocations do at least the scaled work
-- statement:
--   Let $L$ be nonnegative loads, $h$ a nonnegative allocation sequence and $c\in[0,1]$. Let $w$ be the work of $h$ and $\bar w$ the work of the scaled allocations $\bar h_t=c\,h_t$, each with its own queues on the same loads. Then for every user $i$ and every time $t$
--
--   $$
--   \sum_{\tau=1}^t\bar w_\tau(i)\ \ge\ c\sum_{\tau=1}^t w_\tau(i).
--   $$
--
--   With $c=1-4\varepsilon$ and summing over users, this is the step $(1-4\varepsilon)\,\mathrm{work}_h\le\mathrm{work}_{\bar h}$ in the derivation of Theorem 1 from Theorem 3.
--
--   Differences from the source:
--   - generalization: total work over all users with c = 1 − 4ε and Σ_i h_t(i) = 1 → per-user cumulative work, every c ∈ [0, 1], every nonnegative h; reason: summing over users with c = 1 − 4ε gives the paper's statement
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, §3, p. 10 (unnumbered, derivation of Theorem 1 from Theorem 3)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_userWork

namespace CloudAlloc.MWU

/-- **Scaled allocations do at least the scaled work (derivation of Theorem 1, p. 10).**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, §3, p. 10 (unnumbered, in the derivation of Theorem 1 from
Theorem 3): "To argue the second, let `w1, . . . , wT` and `w̄1, . . . , w̄T` respectively denote the
work performed by allocations `h` and `h̄`. Then `(1−4ε)w1, . . . , (1−4ε)wT` are feasible work patterns
that the allocations `h̄1, . . . , h̄T` could do, since in this setting we have `1−4ε` capacity and the
same workload."

For nonnegative loads, nonnegative allocations `h` and a factor `c ∈ [0, 1]`, the allocations
`c·h` do, for every user `i` and every time `t`, at least `c` times the cumulative work that `h`
does: `Σ_{τ≤t} w̄_τ(i) ≥ c · Σ_{τ≤t} w_τ(i)`.

**Formalization Note.** Lean time `τ` is the paper's `τ + 1`. The paper uses `c = 1 − 4ε` and the
total work over all users; the statement is per user and for every `c ∈ [0, 1]` (summing over `i`
gives the paper's form). Each allocation sequence has its own queues on the same loads, from
`Q_1 = 0`. -/
theorem scaled_allocation_work {N : ℕ} {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {hs : ℕ → Fin N → ℝ}
    (hhs : ∀ t i, 0 ≤ hs t i) (i : Fin N) (t : ℕ) :
    c * userWork hs L i t ≤ userWork (fun τ j => c * hs τ j) L i t := by sorry

end CloudAlloc.MWU
