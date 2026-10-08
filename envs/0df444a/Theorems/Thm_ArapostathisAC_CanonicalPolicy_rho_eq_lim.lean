-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalPolicy_rho_eq_lim
-- name    : ArapostathisAC.CanonicalPolicy.rho_eq_lim
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:42:29.100396+00:00
-- url     : https://prove2.me/theorems/7a3ee0a4-6b67-42b8-8adf-4382c2a4afa7
-- title:
--   p. 319 — ρ(x) = lim (1/N) J_N(x, π*) for a canonical triplet (ρ, h, π*)
-- statement:
--   Let $(S, A, U, P, c)$ be a controlled Markov process with Borel state and action spaces and one-stage cost $c \in \mathcal M_b(K)$, and let $(\rho, h, \pi^*)$ be a canonical triplet. Then for every $x \in S$ the limit of the expected average cost of $\pi^*$ exists and equals $\rho(x)$:
--   $$\rho(x) = \lim_{N\to\infty} \frac1N J_N(x, \pi^*).$$
--
--   Together with Theorem 6.3 (i) this gives parts (ii) and (iii): $\rho(x)$ is attained as a genuine limit by $\pi^*$ and no policy does better in the limit inferior.
--
--   **Formalization Note.** The sequence is $J_N(x,\pi^*)/N$ for $N \in \mathbb N$, real valued; the $N = 0$ term is irrelevant to the limit.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 319, proof of Theorem 6.3, display ρ(x) = lim (1/N) J_N(x, π*)

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP

open MeasureTheory ProbabilityTheory Filter Topology

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- p. 319: if `(ρ, h, π*)` is a canonical triplet and `c ∈ 𝓜_b(K)`, then
`ρ(x) = lim_{N → ∞} (1/N) J_N(x, π*)` for every `x ∈ S`. -/
theorem rho_eq_lim (M : BorelCMP S A) (hc : CostBounded M) (ρ h : S → ℝ) (πs : Policy M)
    (hcan : IsCanonical M ρ h πs) (x : S) :
    Tendsto (fun N : ℕ => JN0 M πs N x / N) atTop (𝓝 (ρ x)) := by sorry

end ArapostathisAC.CanonicalPolicy
