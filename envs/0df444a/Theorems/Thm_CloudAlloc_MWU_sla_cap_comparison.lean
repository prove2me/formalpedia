-- Prove2me | Theorems.Thm_CloudAlloc_MWU_sla_cap_comparison
-- name    : CloudAlloc.MWU.sla_cap_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-29T23:46:48.940106+00:00
-- url     : https://prove2.me/theorems/5cbe3894-53a7-48b1-9f1e-03d044c21d7b
-- title:
--   Proof of Theorem 1: a constant $c\,b$ allocation does at least $c$ times the work of any allocation capped at $b$
-- statement:
--   Let $L$ be nonnegative loads, $i$ a user, $b$ a cap and $c\in[0,1]$. Let $h''$ be any allocations with $0\le h''_t(i)\le b$ for all $t$, and $h'$ allocations with $h'_t(i)=c\,b$ for all $t$; let $w''$, $w'$ be their work, each with its own queues on the same loads. Then for every time $t$
--
--   $$
--   \sum_{\tau=1}^t w'_\tau(i)\ \ge\ c\sum_{\tau=1}^t w''_\tau(i).
--   $$
--
--   With $c=1-2\varepsilon$ and $b=\beta(i)$ this turns Theorem 4's comparison with the static reservation $(1-2\varepsilon)\beta(i)$ into clause 2 of Theorem 1, a comparison with every allocation capped at $\beta(i)$.
--
--   Differences from the source:
--   - reading: "a stronger bi-criteria result that implies the SLA guarantee in Theorem 1" (no statement printed) → the comparison step stated explicitly; reason: the implication from Theorem 4 to Theorem 1, clause 2, needs exactly this step
--   - generalization: c = 1 − 2ε, b = β(i), h″ allocations in [0, 1]^N → every c ∈ [0, 1], every b, only coordinate i of h″ and h′ constrained; reason: the paper's case is the instance c = 1 − 2ε, b = β(i)
--   - encoding: times t = 1, 2, … with Q_t, h_t, w_t, L_t → Lean time t is the paper's time t + 1 (h t = h_{t+1}, queue h L t = Q_{t+1}, Finset.range t = {1, …, t}); reason: 0-based indexing of ℕ; same instances
--   - reading: initial queue Q_1 left implicit in the model (p. 3) → every queue starts at 0 (queue h L 0 = 0); reason: LP constraint (1) and Proposition 2 (p. 11) require Σ_{s≤t} w_s(i) ≤ Σ_{s≤t} L_s(i), which fixes Q_1 = 0
-- source:
--   Perez-Salazar, Menache, Singh, Toriello, Dynamic Resource Allocation in the Cloud with Near-Optimal Efficiency, arXiv:1809.02688v3, §3, p. 10 (implicit step from Theorem 4 to Theorem 1)

import Mathlib
import Definitions.Def_CloudAlloc_MWU_userWork

namespace CloudAlloc.MWU

/-- **SLA comparison: a constant `c·b` allocation does at least `c` times the work of any allocation
capped at `b` (the step from Theorem 4 to Theorem 1, p. 10).**
Perez-Salazar, Menache, Singh, Toriello, *Dynamic Resource Allocation in the Cloud with Near-Optimal
Efficiency*, arXiv:1809.02688v3, §3, p. 10 (implicit step): "Similarly, for SLA satisfaction, we
prove a stronger bi-criteria result that implies the SLA guarantee in Theorem 1."

For nonnegative loads, a user `i`, a cap `b`, a factor `c ∈ [0, 1]`, any allocations `h″` giving
user `i` between `0` and `b` at every step, and allocations `h′` giving user `i` exactly `c·b` at every
step: at every time `t`, user `i`'s cumulative work under `h′` is at least `c` times its cumulative
work under `h″`.

**Formalization Note.** Lean time `τ` is the paper's `τ + 1`. The paper does not spell this step out:
with `c = 1 − 2ε` and `b = β(i)` it turns Theorem 4's comparison with `h′_t(i) = (1 − 2ε)β(i)` into
Theorem 1's comparison with every `h′` capped at `β(i)`. It is stated for general `c ∈ [0, 1]` and
`b`. Only coordinate `i` of the allocations enters; each sequence has its own queues on the same loads,
from `Q_1 = 0`. -/
theorem sla_cap_comparison {N : ℕ} {c b : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {L : ℕ → Fin N → ℝ} (hL : ∀ t i, 0 ≤ L t i) (i : Fin N) {h'' h' : ℕ → Fin N → ℝ}
    (hh'' : ∀ τ, 0 ≤ h'' τ i ∧ h'' τ i ≤ b) (hh' : ∀ τ, h' τ i = c * b) :
    ∀ t, c * userWork h'' L i t ≤ userWork h' L i t := by sorry

end CloudAlloc.MWU
