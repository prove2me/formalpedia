-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalPolicy_mandl_nonneg
-- name    : ArapostathisAC.CanonicalPolicy.mandl_nonneg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:02:07.730242+00:00
-- url     : https://prove2.me/theorems/6ec31a0e-ac1d-4500-89f3-12a565d46db2
-- title:
--   p. 319 — Mandl's discrepancy Φ is nonnegative on K for a canonical triplet with constant ρ
-- statement:
--   Let $(S, A, U, P, c)$ be a controlled Markov process with Borel state and action spaces and $c \in \mathcal M_b(K)$. Let $(\rho, h, \pi^*)$ be a canonical triplet with $\rho(x) = \rho^* \in \mathbb R$ for all $x \in S$, and let
--   $$\Phi(x, a) = c(x, a) + \int_S h(y)\,P(dy \mid x, a) - \rho^* - h(x)$$
--   be Mandl's discrepancy function. Then $\Phi(x, a) \ge 0$ for all $(x, a) \in K$.
--
--   This is the inequality half of the average cost optimality equation (6.7) written in terms of $\Phi$; it is what turns the almost-sure identity of the martingale step into the lower bound of Theorem 6.3 (v).
--
--   **Formalization Note.** The paper derives $\Phi \ge 0$ from (6.7), which Theorem 6.2 provides for stationary deterministic $\pi^*$. Here $\pi^*$ is an arbitrary admissible policy and the hypothesis is the canonical triplet itself; the constant $\rho^*$ is the hypothesis of Theorem 6.3 (v).
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 319, proof of Theorem 6.3 (v)–(vi), "due to (6.7), Φ(x, a) ≥ 0 for all (x, a) ∈ K"

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP
import Definitions.Def_ArapostathisAC_CanonicalPolicy_SamplePath

open MeasureTheory ProbabilityTheory Filter Topology

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- p. 319, proof of Theorem 6.3 (v): if `(ρ, h, π*)` is a canonical triplet with `ρ ≡ ρ*`
constant and `c ∈ 𝓜_b(K)`, then Mandl's discrepancy is nonnegative on `K`:
`Φ(x, a) ≥ 0` for all `(x, a) ∈ K`. -/
theorem mandl_nonneg (M : BorelCMP S A) (hc : CostBounded M) (ρ h : S → ℝ) (πs : Policy M)
    (hcan : IsCanonical M ρ h πs) (ρs : ℝ) (hρ : ∀ x, ρ x = ρs) :
    ∀ x, ∀ a ∈ M.U x, 0 ≤ mandl M h ρs (x, a) := by sorry

end ArapostathisAC.CanonicalPolicy
