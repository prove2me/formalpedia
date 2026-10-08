-- Prove2me | Theorems.Thm_DiaconisStroock_OddPaths_proposition_2
-- name    : DiaconisStroock.OddPaths.proposition_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:07:40.602912+00:00
-- url     : https://prove2.me/theorems/86c1adc2-f32c-4095-b85f-520d8d984b0f
-- title:
--   Proposition 2, p. 40 — β_min ≥ −1 + 2/ι for an irreducible aperiodic reversible chain and any system Σ of odd closed paths
-- statement:
--   Let $X$ be a finite set and $P(x,y)$ the transition matrix of an irreducible, aperiodic Markov chain on $X$, reversible with respect to its stationary distribution $\pi$: $Q(x,y)=\pi(x)P(x,y)=\pi(y)P(y,x)$. Let $\beta_{\min}=\beta_{m-1}$ be the smallest eigenvalue of $P$.
--
--   For each $x\in X$ let $\sigma_x$ be a path from $x$ to $x$ with an odd number of edges, along edges $e$ with $Q(e)>0$ (self-loops included) and with no directed edge traversed twice, and let $\Sigma=(\sigma_x)_{x\in X}$. With $|\sigma_x|_Q=\sum_{e\in\sigma_x}Q(e)^{-1}$ and
--
--   $$
--   \iota=\iota(\Sigma)=\max_e\sum_{\sigma_x\ni e}|\sigma_x|_Q\,\pi(x)
--   $$
--
--   (the maximum over directed edges), for every such $\Sigma$:
--
--   $$
--   \beta_{\min}\ge-1+\frac{2}{\iota}.
--   $$
--
--   The aperiodic chain is exactly the case $\beta_{\min}>-1$; this proposition makes that quantitative, and together with Proposition 1 it bounds the absolute spectral gap $1-\beta_*$, $\beta_*=\max(\beta_1,|\beta_{\min}|)$, which governs convergence to stationarity.
--
--   **Formalization Note** $\beta_{\min}$ is the infimum of the real eigenvalues of $P$. The paper defines $|\sigma_x|_Q$ "by analogy with (1.4)", whose paths may not repeat an edge; for §1C's directed edges the rule is read as "no directed edge is traversed twice", which keeps the page's claim that such paths exist for every irreducible aperiodic chain. The system $\Sigma$ is universally quantified, as in "for any choice". No assumption $|X|\ge2$ is made: on a one-point space the bound reads $1\ge1$.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 40, Proposition 2, with (1.4) (p. 37) and (1.7) (p. 40), https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_OddPaths_Iota
open MarkovMixing

namespace DiaconisStroock.OddPaths

theorem proposition_2 {V : Type*} [Fintype V] [DecidableEq V] (P : Matrix V V ℝ)
    (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P) (haper : Aperiodic P) (π : V → ℝ)
    (hπ : IsStationary P π) (hrev : DetailedBalance P π) (S : V → List V)
    (hS : IsOddPathSystem P π S) :
    -1 + 2 / iota P π S ≤ betaMin P := by sorry

end DiaconisStroock.OddPaths
