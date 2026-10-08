-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalPolicy_JN_canonical_le
-- name    : ArapostathisAC.CanonicalPolicy.JN_canonical_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:42:31.763147+00:00
-- url     : https://prove2.me/theorems/18507117-50c3-46ab-bcb2-8fc03c51272b
-- title:
--   Proof of Theorem 6.3 (i) — a canonical policy is optimal for every horizon with terminal cost h
-- statement:
--   Let $(S, A, U, P, c)$ be a controlled Markov process with Borel state and action spaces and one-stage cost $c \in \mathcal M_b(K)$, bounded on the set $K$ of admissible state–action pairs. Let $(\rho, h, \pi^*)$ be a canonical triplet: $\rho, h \in \mathcal M_b(S)$, $\pi^* \in \Pi$, and $J_N(x, \pi^*, h) = J^*_N(x, h) = h(x) + N\rho(x)$ for all $N \in \mathbb N_0$ and $x \in S$. Then for every $N$, every $x \in S$ and every admissible policy $\pi \in \Pi$,
--   $$J_N(x, \pi^*, h) = E^{\pi^*}_x\Big[\sum_{t=0}^{N-1} c(X_t, A_t) + h(X_N)\Big] \le E^{\pi}_x\Big[\sum_{t=0}^{N-1} c(X_t, A_t) + h(X_N)\Big] = J_N(x, \pi, h).$$
--
--   This is the first step of the proof of Theorem 6.3 (i): the canonical policy is $N$-stage optimal for the terminal cost $h$, uniformly in $N$.
--
--   **Formalization Note.** $J^*_N(x, h)$ is a real infimum over all of $\Pi$; the statement asserts that the infimum in (6.4) is a genuine lower bound of every $J_N(x, \pi, h)$.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 318, proof of Theorem 6.3 (i), first display

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP

open MeasureTheory ProbabilityTheory Filter Topology

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Proof of Theorem 6.3 (i), p. 318: if `(ρ, h, π*)` is a canonical triplet and `c ∈ 𝓜_b(K)`,
then `J_N(x, π*, h) ≤ J_N(x, π, h)` for every `N`, every `x` and every `π ∈ Π`. -/
theorem JN_canonical_le (M : BorelCMP S A) (hc : CostBounded M) (ρ h : S → ℝ) (πs : Policy M)
    (hcan : IsCanonical M ρ h πs) (N : ℕ) (x : S) (π : Policy M) :
    JN M πs N h x ≤ JN M π N h x := by sorry

end ArapostathisAC.CanonicalPolicy
