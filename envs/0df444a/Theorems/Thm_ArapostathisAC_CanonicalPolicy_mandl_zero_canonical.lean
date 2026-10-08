-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalPolicy_mandl_zero_canonical
-- name    : ArapostathisAC.CanonicalPolicy.mandl_zero_canonical
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:02:31.196984+00:00
-- url     : https://prove2.me/theorems/50addc4e-ab08-4df1-a731-bed9af1503c3
-- title:
--   p. 319 — for a canonical policy π*, Φ(X_t, A_t) = 0 almost surely under π*
-- statement:
--   Let $(S, A, U, P, c)$ be a controlled Markov process with Borel state and action spaces and $c \in \mathcal M_b(K)$. Let $(\rho, h, \pi^*)$ be a canonical triplet with $\rho(x) = \rho^* \in \mathbb R$ for all $x$, and let $\Phi$ be Mandl's discrepancy function for $(h, \rho^*)$. Then for every initial state $x \in S$ and every time $t \in \mathbb N_0$,
--   $$\Phi(X_t, A_t) = 0, \qquad \mathcal P^{\pi^*}_x\text{-a.s.}$$
--
--   Under the canonical policy the process never incurs a positive discrepancy, so by the martingale step its pathwise average cost converges to $\rho^*$.
--
--   **Formalization Note.** The paper prints "$\mathcal P^\pi_x$-a.s." in this sentence; the measure is that of the canonical policy, $\mathcal P^{\pi^*}_x$, which is what we state. The constant $\rho^*$ is the hypothesis of Theorem 6.3 (v).
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 319, last sentence of the proof of Theorem 6.3

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP
import Definitions.Def_ArapostathisAC_CanonicalPolicy_SamplePath

open MeasureTheory ProbabilityTheory Filter Topology

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- p. 319, proof of Theorem 6.3 (v)–(vi): if `(ρ, h, π*)` is a canonical triplet with `ρ ≡ ρ*`
constant and `c ∈ 𝓜_b(K)`, then `Φ(X_t, A_t) = 0` `𝒫^{π*}_x`-a.s., for every `t` and `x`. -/
theorem mandl_zero_canonical (M : BorelCMP S A) (hc : CostBounded M) (ρ h : S → ℝ)
    (πs : Policy M) (hcan : IsCanonical M ρ h πs) (ρs : ℝ) (hρ : ∀ x, ρ x = ρs) (x : S) (t : ℕ) :
    ∀ᵐ ω ∂(pathMeasure M πs x), mandl M h ρs (ω t) = 0 := by sorry

end ArapostathisAC.CanonicalPolicy
