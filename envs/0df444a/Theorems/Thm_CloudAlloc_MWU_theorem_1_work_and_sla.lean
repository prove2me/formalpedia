-- Prove2me | Theorems.Thm_CloudAlloc_MWU_theorem_1_work_and_sla
-- name    : CloudAlloc.MWU.theorem_1_work_and_sla
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:47:37.773368+00:00
-- url     : https://prove2.me/theorems/2b5fb633-9bf6-4cd5-a231-8d2648d8e2a6
-- title:
--   Theorem 1: Algorithm 1 achieves $(1-\varepsilon)$-approximate work and $(1-2\varepsilon)$-approximate SLA satisfaction
-- statement:
--   Let $N\ge 2$ users share a resource of capacity $1$. Let $0<\varepsilon\le 1/10$ and $0<\eta<1/3$ be the parameters of Algorithm 1, let the SLAs satisfy $\beta(i)\ge 2\varepsilon/N$ and $\sum_i\beta(i)\le 1$, let the loads $L_1,L_2,\dots\in\mathbb R^N_{\ge 0}$ be arbitrary, and let $h$ be a run of Algorithm 1 (from any $h_1\in\Delta_\varepsilon$), with work $w$. Then:
--
--   1. **Approximate work maximization.** For every horizon $T$ and every offline allocation sequence $h^*_1,\dots,h^*_T$ with $h^*_t\ge 0$ and $\sum_i h^*_t(i)\le 1$,
--   $$
--   \mathrm{work}_{\mathrm{alg}}\ \ge\ (1-\varepsilon)\,\mathrm{work}_{h^*_1,\dots,h^*_T}-2000\,\frac{N}{\varepsilon^2\eta}\ln(N/\varepsilon).
--   $$
--   2. **Approximate SLA satisfaction.** With $\tilde p=32\,\frac{N^2}{\varepsilon^3\eta}\ln(N/\varepsilon)$, for every user $i$, every time $t$ and every allocation sequence $h'$ with $0\le h'_\tau(i)\le\beta(i)$ for all $\tau$, with work $w'$,
--   $$
--   \sum_{\tau=1}^t w_\tau(i)\ \ge\ (1-2\varepsilon)\sum_{\tau=1}^t w'_\tau(i)-\beta(i)\,\tilde p .
--   $$
--
--   With only binary feedback (which queues are empty), the online multiplicative weights rule nearly matches the best dynamic offline allocation in total work, while giving each user nearly the work of its SLA reservation.
--
--   **Formalization Note** The paper's derivation on p. 10 reaches the factor $(1-4\varepsilon)$ in clause 1 when the algorithm runs at $\varepsilon$; the statement keeps the printed $(1-\varepsilon)$.
--
--   Differences from the source:
--   - generalization: O(Nε^{−2} log(N/ε)) and p̃ = p̃(N, ε) = O(N²ε^{−3} log(N/ε)) → 2000·N/(ε²η)·ln(N/ε) and p̃ = 32·N²/(ε³η)·ln(N/ε); reason: the paper's explicit constants (p. 10); they imply the O-forms for every fixed η, the O hiding the factor 1/η
--   - reading: "for any input parameter 0 < ε ≤ 1/10 … Algorithm 1 achieves"; the p. 10 derivation applies Theorem 3 at ε/4 → Algorithm 1 run at the ε of the statement in both clauses; reason: the statement runs the algorithm at its input ε; running it at ε/4 would change clause 2's p̃
--   - generalization: an optimal offline sequence h* ∈ [0, 1]^N with Σ_i h*_t(i) = 1 → every nonnegative sequence with Σ_i h*_t(i) ≤ 1; reason: an optimum exists and dominates every such sequence, so the statement specializes to the printed benchmark
--   - generalization: h′_1, …, h′_T ∈ [0, 1]^N with h′_t(i) ≤ β(i) → only coordinate i constrained: 0 ≤ h′ τ i ≤ β(i); reason: user i's work under h′ depends only on coordinate i
--   - encoding: horizon T, loads L_1, …, L_T, any time t → infinite load sequence and run; clause 1 for every T, clause 2 for every t; reason: the run up to T does not depend on later loads; same instances
--   - reading: w_t(i) = min{h_t(i), L_t(i) + Q_t(i)} (p. 3) and the remark "h_t(i) = w_t(i) for all active users" (p. 8) → work is min{h, L + Q}; nothing like w = h for active users is assumed; reason: the p. 3 definition is binding; the p. 8 remark is false when L_t(i) + Q_t(i) < h_t(i)
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, Theorem 1, p. 5 (explicit constants: reduction display after Theorem 3 and Theorem 4, p. 10)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_IsAlg1Run
import Definitions.Def_CloudAlloc_MWU_totalWork
import Definitions.Def_CloudAlloc_MWU_userWork

namespace CloudAlloc.MWU

/-- **Theorem 1: near-optimal work and approximate SLA satisfaction of Algorithm 1.**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, Theorem 1, p. 5 (constants from p. 10):
"For any input parameter `0 < ε ≤ 1/10`, SLAs `β = (β(1), . . . , β(N))` satisfying `β(i) ≥ 2ε/N`, and
online loads `L1, . . . , LT ∈ R^N_{≥0}`, Algorithm 1 achieves the following guarantees:
1. Approximate Work Maximization. Let `h∗1, . . . , h∗T ∈ [0, 1]^N` be an optimal offline sequence of
allocations such that `Σ_i h∗t(i) = 1` for all `1 ≤ t ≤ T`. Then
`work_alg ≥ (1 − ε) work_{h∗1,...,h∗T} − O(Nε^{−2} log(N/ε))`.
2. Approximate SLA Satisfaction. There exists `p̃ = p̃(N, ε) = O(N²ε^{−3} log(N/ε))` such that for any
user `i` and time `t`, if we take `h′1, . . . , h′T ∈ [0, 1]^N` to be any sequence of allocations with
`h′t(i) ≤ β(i)`, then `Σ_{τ=1}^t wτ(i) ≥ (1 − 2ε) Σ_{τ=1}^t w′τ(i) − β(i)p̃`, where `w′t` is the work
performed by the allocations `h′1, . . . , h′T`."

For every run of Algorithm 1 with `N ≥ 2`, `0 < ε ≤ 1/10`, `0 < η < 1/3`, SLAs `β(i) ≥ 2ε/N` with
`Σβ ≤ 1` and nonnegative loads:
(1) for every horizon `T` and every offline allocation sequence `h*` (nonnegative, summing to at most
`1` at each step), `work_alg ≥ (1 − ε)·work_{h*} − 2000N/(ε²η)·ln(N/ε)`;
(2) for every user `i`, time `t` and allocation sequence `h′` with `0 ≤ h′_τ(i) ≤ β(i)`,
`Σ_{τ≤t} w_τ(i) ≥ (1 − 2ε)·Σ_{τ≤t} w′_τ(i) − β(i)·32N²/(ε³η)·ln(N/ε)`.

**Formalization Note.** Lean time `t` is the paper's `t + 1` (`h 0` is `h_1`; `totalWork h L T` and
`userWork h L i t` are the paper's sums over `1, …, T` and `1, …, t`). Algorithm 1 is run at the `ε`
of the statement in both clauses. The O-terms are the explicit constants of p. 10: `2000N/(ε²η)·ln(N/ε)`
from the reduction display after Theorem 3 and `p̃ = 32N²/(ε³η)·ln(N/ε)` from Theorem 4; the O hides
the factor `1/η`. The benchmark `h*` is any sequence with `Σ_i h*_t(i) ≤ 1` (equivalent to the optimal
one with `Σ = 1`, since work is monotone in the allocation); each benchmark has its own queues on the
same loads, from `Q_1 = 0`. In clause 2 only coordinate `i` of `h′` is constrained (only it enters
`w′_τ(i)`), and `t` ranges over all times (the run is infinite). `ln`/`log` are `Real.log`.
The paper's derivation on p. 10 reaches `(1 − 4ε)` in clause 1 with the algorithm at `ε`; the
statement keeps the printed `(1 − ε)`. -/
theorem theorem_1_work_and_sla {N : ℕ} (hN : 2 ≤ N) {ε η : ℝ} (hε : 0 < ε) (hε' : ε ≤ 1 / 10)
    (hη : 0 < η) (hη' : η < 1 / 3)
    {β : Fin N → ℝ} (hβ : ∀ i, 2 * ε / N ≤ β i) (hβsum : ∑ i, β i ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) {h : ℕ → Fin N → ℝ}
    (hrun : IsAlg1Run N ε η β L h) :
    (∀ (T : ℕ) (hs : ℕ → Fin N → ℝ), (∀ t < T, (∀ i, 0 ≤ hs t i) ∧ ∑ i, hs t i ≤ 1) →
        (1 - ε) * totalWork hs L T - 2000 * (N : ℝ) / (ε ^ 2 * η) * Real.log ((N : ℝ) / ε)
          ≤ totalWork h L T) ∧
      (∀ (i : Fin N) (t : ℕ) (h' : ℕ → Fin N → ℝ), (∀ τ, 0 ≤ h' τ i ∧ h' τ i ≤ β i) →
        (1 - 2 * ε) * userWork h' L i t
            - β i * (32 * (N : ℝ) ^ 2 / (ε ^ 3 * η) * Real.log ((N : ℝ) / ε))
          ≤ userWork h L i t) := by sorry

end CloudAlloc.MWU
