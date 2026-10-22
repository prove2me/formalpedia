-- Prove2me | Theorems.Thm_ChoiceCDLP_Efficient_cdlp_dual_zero_reduced_cost
-- name    : ChoiceCDLP.Efficient.cdlp_dual_zero_reduced_cost
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-03T07:27:49.990373+00:00
-- url     : https://prove2.me/theorems/56928854-2ba6-4491-8f62-695646a122c6
-- title:
--   Proof of Proposition 4 — an optimal CDLP dual prices the column of a set with t*(T) > 0 at reduced cost zero
-- statement:
--   Consider the CDLP with arrival probability $0 < \lambda \le 1$, capacities $c \ge 0$ and horizon $\tau \ge 0$, and its dual
--   $$\min\ \pi^\top c + \tau\sigma \quad\text{s.t.}\quad \lambda \pi^\top Q(S) + \sigma \ge \lambda R(S)\ \ \forall S \subseteq N,\qquad \pi \ge 0,\ \ \sigma \ge 0 .$$
--   The **reduced cost** of the column $S$ at dual prices $(\pi, \sigma)$ is $\lambda R(S) - \lambda \pi^\top Q(S) - \sigma$.
--
--   Let $t^*$ be an optimal solution of the CDLP and $T$ an offer set with $t^*(T) > 0$. Then there is an optimal solution $(\pi^*, \sigma^*)$ of the dual: $\pi^* \ge 0$, $\sigma^* \ge 0$,
--   $$\lambda R(S) - \lambda \pi^{*\top} Q(S) - \sigma^* \le 0 \quad \forall S \subseteq N, \qquad \pi^{*\top} c + \tau \sigma^* = \sum_S \lambda R(S)\, t^*(S),$$
--   at which the column $T$ has reduced cost zero:
--   $$\lambda R(T) - \lambda \pi^{*\top} Q(T) - \sigma^* = 0 .$$
--
--   This is the linear-programming step of the paper's proof of Proposition 4: dual feasibility bounds the reduced cost of every column by zero, and the column of a set used for positive time has reduced cost exactly zero.
--
--   **Formalization Note.** The paper says "$T$ is part of the optimal basis"; the statement here is for every optimal solution $t^*$, basic or not, which is what Proposition 4 needs (the zero reduced cost follows for any optimal primal–dual pair). Dual optimality is expressed by equality of the dual objective with the primal optimal value.
-- source:
--   Liu, van Ryzin, On the Choice-Based Linear Programming Model for Network Revenue Management, Manuf. Serv. Oper. Manag. 10(2), 2008, p. 296, proof of Proposition 4 (reduced cost and the display following 'by (3) they must satisfy'); dual (3), p. 293

import Mathlib
import Definitions.Def_ChoiceCDLP_Efficient_ChoiceNetwork
import Definitions.Def_ChoiceCDLP_Efficient_cdlpOptimal

namespace ChoiceCDLP.Efficient

/-- Proof of Proposition 4 (p. 296): if `t*` is an optimal solution of the CDLP (2) with
`t*(T) > 0`, then there is an optimal solution `(π*, σ*)` of the dual (3) — `π* ≥ 0`, `σ* ≥ 0`,
`lam π*ᵀ Q(S) + σ* ≥ lam R(S)` for every `S`, with dual objective `π*ᵀ c + τ σ*` equal to the
optimal CDLP value — at which the column `T` has reduced cost
`lam R(T) − lam π*ᵀ Q(T) − σ* = 0`. -/
theorem cdlp_dual_zero_reduced_cost {m n : ℕ} (N : ChoiceNetwork m n)
    (lam : ℝ) (hlam_pos : 0 < lam) (hlam_le : lam ≤ 1)
    (c : Fin m → ℝ) (hc : 0 ≤ c) (τ : ℝ) (hτ : 0 ≤ τ)
    (t : Finset (Fin n) → ℝ) (ht : IsCDLPOptimal N lam c τ t)
    (T : Finset (Fin n)) (hT : 0 < t T) :
    ∃ (π : Fin m → ℝ) (σ : ℝ), 0 ≤ π ∧ 0 ≤ σ ∧
      (∀ S : Finset (Fin n),
        lam * revenue N S - lam * dotProduct π (consumption N S) - σ ≤ 0) ∧
      dotProduct π c + τ * σ = cdlpObjective N lam t ∧
      lam * revenue N T - lam * dotProduct π (consumption N T) - σ = 0 := by sorry

end ChoiceCDLP.Efficient
