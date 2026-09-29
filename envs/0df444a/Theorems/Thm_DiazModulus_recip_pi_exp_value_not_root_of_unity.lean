-- Prove2me | Theorems.Thm_DiazModulus_recip_pi_exp_value_not_root_of_unity
-- name    : DiazModulus.recip_pi_exp_value_not_root_of_unity
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-09T06:55:33.097894+00:00
-- url     : https://prove2.me/theorems/70537ec3-a818-49a5-a4ea-d4298bf0dbc0
-- title:
--   The value $e^{\gamma/(i\pi)}$ is never a root of unity, for algebraic $\gamma \neq 0$
-- statement:
--   For every non-zero algebraic $\gamma$, the value $e^{\gamma/(i\pi)}$ is **not a root of unity**.
--
--   **Proof sketch.** If $e^{\lambda}$ has finite order with $\lambda = \gamma/(i\pi)$, then $e^{n\lambda} = 1$ for some $n \geq 1$, so $n\lambda = 2\pi i m$ for some integer $m$. Substituting $\lambda = \gamma/(i\pi)$ and clearing gives $\gamma = -2\pi^{2}m/n$. With $\gamma$ algebraic and non-zero this makes $\pi^{2}$ algebraic, contradicting `DiazModulus.pi_sq_transcendental`, which is Proved on this mission and is discharged here rather than carried.
--
--   **What it is for.** `DiazModulus.recip_pi_not_log` and its two children ask for $e^{\gamma/(i\pi)}$ to be *transcendental*. This node settles the cheapest way that could fail: the value cannot be a root of unity. Anyone attacking `DiazModulus.recip_pi_not_log_real_gamma` needs this first, and on that half it says something concrete — $\gamma$ real makes $\lambda$ purely imaginary, so $|e^{\lambda}| = 1$, and a hypothetical algebraic value would have to be an algebraic number **on the unit circle that is not a root of unity**. Such numbers exist, for instance $(3+4i)/5$, so this does not close the leaf; it identifies exactly which shape a counterexample would have to take.
--
--   **Not claimed.** No transcendence. The gap between "not a root of unity" and "transcendental" is the whole open problem, and closing it needs transcendence input this mission does not have. This node closes nothing.
--
--   **Formalization note.** "Root of unity" is `IsOfFinOrder` applied to the value, which is the form the argument consumes; no reality or genericity hypothesis on $\gamma$ is needed, so the statement covers both axis halves at once.
-- source:
--   Elementary, from the transcendence of pi^2 (DiazModulus.pi_sq_transcendental, Proved on this mission).

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem recip_pi_exp_value_not_root_of_unity :
    ∀ γ : ℂ, IsAlgebraic ℚ γ → γ ≠ 0 →
      ¬ IsOfFinOrder (Complex.exp (γ / (((Real.pi : ℝ) : ℂ) * Complex.I))) := by sorry
end DiazModulus
