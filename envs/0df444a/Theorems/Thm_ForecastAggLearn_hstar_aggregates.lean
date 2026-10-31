-- Prove2me | Theorems.Thm_ForecastAggLearn_hstar_aggregates
-- name    : ForecastAggLearn.hstar_aggregates
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:26:27.814679+00:00
-- url     : https://prove2.me/theorems/4e1e6ce9-4002-4e8d-8ca4-d09731bc0065
-- title:
--   §4.2.1 — for injective $A$, $A^\top A$ is invertible and $\mathbf 1_m\cdot\tilde y=h^*\cdot A\tilde y$
-- statement:
--   Let $A$ be a real $n\times m$ matrix such that $y\mapsto Ay$ is injective. Then $A^\top A$ is invertible, and with $h^*=A(A^\top A)^{-1}\mathbf 1_m$,
--
--   $$
--   \mathbf 1_m\cdot\tilde y=h^*\cdot(A\tilde y)\qquad\text{for every }\tilde y\in\mathbb R^m .
--   $$
--
--   Adding $\tilde\mu$ to both sides gives the paper's display $\mathbf 1_m\cdot\tilde y+\tilde\mu=h^*\cdot\tilde z+\tilde\mu$ with $\tilde z=A\tilde y$: the Bayes-optimal aggregate is a fixed linear function of what the prior-aware aggregator observes. This is why the aggregation can be learned when $A$ is injective.
--
--   Differences from the source:
--   - generalization: A the 0/1 evidence matrix → any real n × m matrix with injective mulVec; reason: the evidence matrix is the 0/1 case
--   - encoding: chain 1_m·ỹ + µ̃ = 1_m^⊤A_l^{−1}Aỹ + µ̃ = (A_l^{−1⊤}1_m)·z̃ + µ̃ = h*·z̃ + µ̃ → its two ends without the common term µ̃: h* ⬝ᵥ (Aỹ) = Σ_j ỹ_j; reason: adding µ̃ to both sides is the same identity; the middle terms are the definition of h*
-- source:
--   Babichenko, Garber, Learning of Optimal Forecast Aggregation in Partial Evidence Environments, arXiv:1802.07107v1, §4.2.1, display, p.17

import Mathlib
import Definitions.Def_ForecastAggLearn_hstar

namespace ForecastAggLearn

/-- **The optimal aggregation is linear in `z̃ = Aỹ`.**
Babichenko, Garber, arXiv:1802.07107v1, §4.2.1, display, p.17: "In case A is injective it holds
that A^⊤A is invertible, and hence, denoting the left inverse of A by A_l^{−1} := (A^⊤A)^{−1}A^⊤,
the optimal aggregation has the form
1_m · ỹ + µ̃ = 1_m^⊤ A_l^{−1} Aỹ + µ̃ = (A_l^{−1⊤} 1_m) · z̃ + µ̃ = h* · z̃ + µ̃."

If `A` is injective then `A^⊤A` is invertible and `h* · (Aỹ) = 1_m · ỹ` for every `ỹ ∈ ℝ^m`.

**Formalization Note.** Stated for every real `n × m` matrix with injective `mulVec`; the
evidence matrix is the 0/1 case. The `µ̃` on both sides cancels and is omitted. -/
theorem hstar_aggregates {n m : ℕ} (A : Matrix (Fin n) (Fin m) ℝ)
    (hA : Function.Injective A.mulVec) :
    IsUnit (A.transpose * A).det ∧ ∀ y : Fin m → ℝ, hstar A ⬝ᵥ A.mulVec y = ∑ j, y j := by sorry

end ForecastAggLearn
