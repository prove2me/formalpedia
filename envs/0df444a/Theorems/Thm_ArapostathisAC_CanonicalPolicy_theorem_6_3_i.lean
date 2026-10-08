-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalPolicy_theorem_6_3_i
-- name    : ArapostathisAC.CanonicalPolicy.theorem_6_3_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T07:42:48.827588+00:00
-- url     : https://prove2.me/theorems/4ca37dc8-2576-40b2-91a7-7ff223379ce8
-- title:
--   Theorem 6.3 (i) — J_N(x, π*) ≤ J_N(x, π) + span(h) for a canonical policy π*
-- statement:
--   Let $(S, A, U, P, c)$ be a controlled Markov process with Borel state and action spaces and one-stage cost $c \in \mathcal M_b(K)$. Let $(\rho, h, \pi^*)$ be a canonical triplet. Then for each $x \in S$, every horizon $N \in \mathbb N_0$ and every admissible policy $\pi \in \Pi$,
--   $$J_N(x, \pi^*) \le J_N(x, \pi) + \operatorname{span}(h),$$
--   where $J_N(x,\pi) = E^\pi_x\big[\sum_{t=0}^{N-1} c(X_t, A_t)\big]$ and $\operatorname{span}(h) = \sup_{w, w'} \{h(w) - h(w')\}$.
--
--   The bound holds for every finite horizon with the explicit constant $\operatorname{span}(h)$, independent of $N$ and $\pi$. Dividing by $N$ and letting $N \to \infty$ is what gives parts (ii) and (iii) of Theorem 6.3.
--
--   **Formalization Note.** $\operatorname{span}(h)$ is $\sup h - \inf h$ with real suprema, meaningful because $h$ is bounded (part of the definition of a canonical triplet).
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 318, Theorem 6.3 (i) and its proof

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP

open MeasureTheory ProbabilityTheory Filter Topology

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- Theorem 6.3 (i), p. 318: if `(ρ, h, π*)` is a canonical triplet and `c ∈ 𝓜_b(K)`, then
`J_N(x, π*) ≤ J_N(x, π) + span(h)` for every `x ∈ S`, every `N` and every `π ∈ Π`. -/
theorem theorem_6_3_i (M : BorelCMP S A) (hc : CostBounded M) (ρ h : S → ℝ) (πs : Policy M)
    (hcan : IsCanonical M ρ h πs) (x : S) (N : ℕ) (π : Policy M) :
    JN0 M πs N x ≤ JN0 M π N x + span h := by sorry

end ArapostathisAC.CanonicalPolicy
