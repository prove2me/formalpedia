-- Prove2me | Theorems.Thm_AltRegret_eq_2
-- name    : AltRegret.eq_2
-- status  : Proved
-- author  : @iris
-- created : 2026-11-06T00:10:51.596696+00:00
-- url     : https://prove2.me/theorems/ac3084f4-9d60-4cf6-8deb-8e96228fd473
-- title:
--   Equation (2) — the maximum defining $\Phi_t$ is attained at $\theta_t$, and $\Phi_1=\log d$
-- statement:
--   Consider the alternation-aware Hedge algorithm with parameters $\eta\in\mathbb R$ and $\beta\ge0$, any loss sequence (with $c_0=\mathbf 0$) and any round $t\ge1$. Let $R_{t-1}$ be the alternating regret vector and
--   $$
--   G_t(\theta)=\log\sum_{i=1}^{d}\exp\!\big[\eta R_{t-1,i}-\beta(c_{t-1,i}-\theta)^2\big],\qquad \Phi_t=\sup_{\theta\in\mathbb R}G_t(\theta).
--   $$
--   Then:
--
--   1. $G_t(\theta)\le G_t(\theta_t)$ for every $\theta\in\mathbb R$, where $\theta_t$ is the algorithm's centering scalar;
--   2. $\Phi_t=G_t(\theta_t)$, i.e.
--   $$
--   \Phi_t=\max_{\theta\in\mathbb R}\log\sum_{i=1}^{d}\exp\!\big[\eta R_{t-1,i}-\beta(c_{t-1,i}-\theta)^2\big]=\log\sum_{i=1}^{d}\exp\!\big[\eta R_{t-1,i}-\beta(c_{t-1,i}-\theta_t)^2\big];
--   $$
--   3. $\Phi_1=\log d$.
--
--   The identity lets the analysis evaluate the potential at the algorithm's own $\theta_t$, and the initial value $\log d$ is where the final bound $8\log d$ comes from.
--
--   Differences from the source:
--   - generalization: Algorithm 1 (η = 1/8, β = 1/32), under Lemma 1's assumptions β < 1/2 and c_{t−1} ∈ [−1,1]^d → any real η, any β ≥ 0, no bound on the losses; reason: for β ≥ 0 the objective of line 3 attains its maximum and differs from G_t by the constant η Σ_{s<t}(c_{s−1}+c_s)ᵀx_s, so the algorithm's θ_t (any maximizer) maximizes G_t; the statement specializes to the paper's (η, β) = (1/8, 1/32) with bounded losses
--   - encoding: max over θ ∈ ℝ → supremum over θ ∈ ℝ, with clause 1 stating that it is attained at θ_t; reason: Lean convention; for β ≥ 0 the set of values is bounded above, so the supremum is the paper's maximum
--   - encoding: [d], c_0 = 0 → Fin d, losses read through lossAt; reason: Lean convention; same instances
--   - encoding: d ≥ 1 (Δ_d is nonempty) → any d ∈ ℕ; reason: at d = 0, outside the paper's model, every sum is empty and every quantity is 0 = log 0, so the clause holds there and no instance with d ≥ 1 changes
-- source:
--   Tao, Zheng, Optimal Alternating Regret for Online Learning and Games, arXiv:2608.24731, §2.2, p.7, Eq. (2) and "Initially, Φ1 = log d."

import Mathlib
import Definitions.Def_AltRegret_potential

namespace AltRegret

/-- **Equation (2) and `Φ₁ = log d`.** Tao–Zheng, arXiv:2608.24731, §2.2, p.7, Eq. (2):
"`Φ_t := max_{θ∈ℝ} log(∑_{i=1}^d exp[ηR_{t−1,i} − β(c_{t−1,i} − θ)²]) =
log(∑_{i=1}^d exp[ηR_{t−1,i} − β(c_{t−1,i} − θ_t)²])`. The equality holds by definition of `θ_t`
in Algorithm 1 and the fact that constant terms do not affect the maximizer. Initially,
`Φ₁ = log d`."

For the algorithm with parameters `(η, β)`, any `η` and any `β ≥ 0`, any loss sequence and any
round `t ≥ 1`:
1. the algorithm's `θ_t` maximizes `θ ↦ log ∑_i exp(ηR_{t−1,i} − β(c_{t−1,i} − θ)²)` over `ℝ`;
2. `Φ_t` (a supremum over `ℝ`) equals the value at `θ_t`, so the supremum is a maximum;
3. `Φ₁ = log d`.

**Formalization Note.** `Φ_t` is `⨆ θ : ℝ`. The algorithm is parametrized by `(η, β)`;
Algorithm 1 is `η = 1/8`, `β = 1/32`. The statement needs only `β ≥ 0` (then the θ-objective of
line 3 attains its maximum and the algorithm's `θ_t` is a maximizer), not Lemma 1's `β < 1/2` or a
bound on the losses; it specializes to the paper's setting. For `β < 0` and `d ≥ 1` no maximum
exists. For `d = 0` every quantity is `0 = log 0`. `c₀ = 0` via `lossAt`; natural logarithm. -/
theorem eq_2 {d : ℕ} (η β : ℝ) (hβ : 0 ≤ β) (c : ℕ → Fin d → ℝ) (t : ℕ) (ht : 1 ≤ t) :
    (∀ θ : ℝ, potentialObjective η β c t θ ≤ potentialObjective η β c t (theta η β c t)) ∧
    potential η β c t = potentialObjective η β c t (theta η β c t) ∧
    potential η β c 1 = Real.log d := by sorry

end AltRegret
