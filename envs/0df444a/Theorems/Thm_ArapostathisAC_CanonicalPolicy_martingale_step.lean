-- Prove2me | Theorems.Thm_ArapostathisAC_CanonicalPolicy_martingale_step
-- name    : ArapostathisAC.CanonicalPolicy.martingale_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T08:02:35.652633+00:00
-- url     : https://prove2.me/theorems/c6221d5c-28da-41a5-b484-088037386538
-- title:
--   p. 319 — (1/N)Σc(X_t, A_t) − ρ* − (1/N)ΣΦ(X_t, A_t) → 0 almost surely under every policy
-- statement:
--   Let $(S, A, U, P, c)$ be a controlled Markov process with Borel state and action spaces and $c \in \mathcal M_b(K)$, let $h \in \mathcal M_b(S)$, let $\rho^* \in \mathbb R$, and let $\Phi(x,a) = c(x,a) + \int_S h(y)\,P(dy\mid x,a) - \rho^* - h(x)$. Then for every admissible policy $\pi \in \Pi$ and every initial state $x \in S$,
--   $$\lim_{N\to\infty}\Big[\frac1N\sum_{t=0}^{N-1} c(X_t, A_t) - \rho^* - \frac1N\sum_{t=0}^{N-1}\Phi(X_t, A_t)\Big] = 0, \qquad \mathcal P^\pi_x\text{-a.s.}$$
--
--   This is the probabilistic core of Theorem 6.3 (v)–(vi): pathwise, the average cost differs from $\rho^*$ by the average discrepancy, up to a term that vanishes almost surely.
--
--   **Formalization Note.** The statement is posed exactly as the page displays it, for an arbitrary bounded measurable $h$ and real $\rho^*$; the page's argument uses only the boundedness of $c$, $h$ and $\Phi$, not that $(\rho^*, h)$ comes from a canonical triplet.
-- source:
--   Arapostathis, Borkar, Fernández-Gaucherand, Ghosh, Marcus, Discrete-time controlled Markov processes with average cost criterion: a survey, SIAM J. Control Optim. 31(2) (1993), p. 319, proof of Theorem 6.3 (v)–(vi), display after "Therefore, by the boundedness of h(·)"

import Mathlib
import Definitions.Def_ArapostathisAC_CanonicalPolicy_CMP
import Definitions.Def_ArapostathisAC_CanonicalPolicy_SamplePath

open MeasureTheory ProbabilityTheory Filter Topology

namespace ArapostathisAC.CanonicalPolicy

variable {S A : Type*} [MeasurableSpace S] [StandardBorelSpace S]
  [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]

/-- p. 319, proof of Theorem 6.3 (v): for `c ∈ 𝓜_b(K)`, `h ∈ 𝓜_b(S)`, a constant `ρ*`, every
policy `π ∈ Π` and every initial state `x`,
`lim_{N → ∞} [ (1/N) ∑_{t<N} c(X_t, A_t) - ρ* - (1/N) ∑_{t<N} Φ(X_t, A_t) ] = 0`, `𝒫^π_x`-a.s. -/
theorem martingale_step (M : BorelCMP S A) (hc : CostBounded M) (h : S → ℝ)
    (hh : IsBoundedMeas h) (ρs : ℝ) (π : Policy M) (x : S) :
    ∀ᵐ ω ∂(pathMeasure M π x),
      Tendsto (fun N : ℕ => avgPathCost M N ω - ρs -
        (N : ℝ)⁻¹ * ∑ t ∈ Finset.range N, mandl M h ρs (ω t)) atTop (𝓝 0) := by sorry

end ArapostathisAC.CanonicalPolicy
