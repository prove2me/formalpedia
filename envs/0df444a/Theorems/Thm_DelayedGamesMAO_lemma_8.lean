-- Prove2me | Theorems.Thm_DelayedGamesMAO_lemma_8
-- name    : DelayedGamesMAO.lemma_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:26:41.310665+00:00
-- url     : https://prove2.me/theorems/765dd9c2-e2a0-4aae-a4fa-18637dea0a7c
-- title:
--   Lemma 8 — the adaptive tuning bound $\eta_{T+1}\le\sqrt{2\sum_t\lambda_t/\alpha_t}$
-- statement:
--   Let $T\ge1$ and $(d_t)$ delays with $t+d_t\le T$. Let $\lambda_1,\dots,\lambda_T\ge0$, $\gamma>0$ with $\gamma\ge\sqrt{\max_t\lambda_t}$, and $\alpha_1,\dots,\alpha_T>0$ with $\alpha_t\le1/q_t$. Let $\eta_1=0$ and, for $t\in[T]$,
--   $$
--   \eta_{t+1}=\eta_t+\sum_{s\in N_t}\frac{\lambda_s}{\gamma+\eta_s\alpha_s}.
--   $$
--   Then $0=\eta_1\le\dots\le\eta_{T+1}$, $\eta_{t+1}=\sum_{s\in O_{t+1}}\lambda_s/(\gamma+\eta_s\alpha_s)$ for $t\in[T]$, and
--   $$
--   \eta_{T+1}=\sum_{t=1}^T\frac{\lambda_t}{\gamma+\eta_t\alpha_t}\le\sqrt{2\sum_{t=1}^T\frac{\lambda_t}{\alpha_t}} .
--   $$
--
--   With $\lambda_t=\|g_t-h_t\|_*^2/M$ and $\alpha_t=1/\kappa_t$ this is the step from the master bound to Theorem 1.
--
--   **Formalization Note** $\gamma\ge\sqrt{\max_t\lambda_t}$ is written $\lambda_t\le\gamma^2$ for every $t\in[T]$.
--
--   Differences from the source:
--   - generalization: γ ≥ √(max_t λ_t) > 0 → γ > 0 and λ_t ≤ γ² for every t ∈ [T] (max_t λ_t = 0 allowed); reason: the paper's hypothesis implies these, so the statement specializes to it
--   - encoding: 'Define 0 = η_1 ≤ ⋯ ≤ η_{T+1} such that η_{t+1} = η_t + … = ∑_{s∈O_{t+1}} …' → η_1 = 0 and the first recursion as hypotheses; monotonicity and the second expression as conclusions; reason: the recursion determines η, and the other two properties follow from it; same instances
--   - encoding: the protocol's standing assumption that g_t is revealed at the end of round t + d_t ≤ T (p.3, footnote 1) → hypothesis ∀ t ∈ [T], t + d t ≤ T; reason: part of the model stated once in §2; no instance of the paper is excluded
--   - encoding: rounds 1, …, T (and T + 1) and finite sequences indexed by them → natural numbers and sequences ℕ → … whose terms outside the used indices are unconstrained; reason: only the paper's indices are read; same instances
-- source:
--   Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, Optimal Learning in Games with Arbitrary Delays: Best-of-Both-Worlds for Self-Play and Adversarial Opponents, STOC 2027 submission (manuscript sha256 d17ba8b0…1247), Appendix D, Lemma 8, p.39

import Mathlib
import Definitions.Def_DelayedGamesMAO_observed
import Definitions.Def_DelayedGamesMAO_newObs
import Definitions.Def_DelayedGamesMAO_q

set_option autoImplicit false

namespace DelayedGamesMAO

/-- **Lemma 8 (the adaptive tuning bound).**
Esposito–Jacobsen–Qiu–Ryabchenko–Zhang, *Optimal Learning in Games with Arbitrary Delays:
Best-of-Both-Worlds for Self-Play and Adversarial Opponents*, STOC 2027 submission manuscript
(sha256 d17ba8b0…1247), Appendix D, Lemma 8, p.39: "Let `λ_1, …, λ_T ≥ 0`, let `γ ≥ √(max_t λ_t) > 0`, and let
`α_1, …, α_T > 0` satisfy `α_t ≤ 1/q_t` for every `t ∈ [T]`. Define `0 = η_1 ≤ ⋯ ≤ η_{T+1}` such
that, for all `t ∈ [T]`, `η_{t+1} = η_t + ∑_{s∈N_t} λ_s/(γ + η_s α_s) = ∑_{s∈O_{t+1}} λ_s/(γ + η_s α_s)`.
Then, `η_{T+1} = ∑_{t=1}^T λ_t/(γ + η_t α_t) ≤ √(2 ∑_{t=1}^T λ_t/α_t)`."

**Formalization Note.** `γ ≥ √(max_t λ_t)` is `λ_t ≤ γ²` for every `t ∈ [T]`, with `γ > 0`;
the printed strict positivity of `max_t λ_t` is not required. The sequence is defined by
`η_1 = 0` and the first recursion; its monotonicity and the second expression are conclusions.
The protocol's `t + d_t ≤ T` is a hypothesis. -/
theorem lemma_8 (T : ℕ) (hT : 1 ≤ T) (d : ℕ → ℕ) (hd : ∀ t ∈ Finset.Icc 1 T, t + d t ≤ T)
    (lam : ℕ → ℝ) (hlam : ∀ t ∈ Finset.Icc 1 T, 0 ≤ lam t)
    (γ : ℝ) (hγ : 0 < γ) (hγlam : ∀ t ∈ Finset.Icc 1 T, lam t ≤ γ ^ 2)
    (α : ℕ → ℝ) (hα : ∀ t ∈ Finset.Icc 1 T, 0 < α t ∧ α t ≤ 1 / (q d t : ℝ))
    (η : ℕ → ℝ) (hη1 : η 1 = 0)
    (hη : ∀ t ∈ Finset.Icc 1 T,
      η (t + 1) = η t + ∑ s ∈ newObs d t, lam s / (γ + η s * α s)) :
    (∀ t ∈ Finset.Icc 1 T, η t ≤ η (t + 1)) ∧
      (∀ t ∈ Finset.Icc 1 T, η (t + 1) = ∑ s ∈ observed d (t + 1), lam s / (γ + η s * α s)) ∧
      η (T + 1) = ∑ t ∈ Finset.Icc 1 T, lam t / (γ + η t * α t) ∧
      η (T + 1) ≤ Real.sqrt (2 * ∑ t ∈ Finset.Icc 1 T, lam t / α t) := by sorry

end DelayedGamesMAO
