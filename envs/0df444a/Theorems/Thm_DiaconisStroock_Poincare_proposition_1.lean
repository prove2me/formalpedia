-- Prove2me | Theorems.Thm_DiaconisStroock_Poincare_proposition_1
-- name    : DiaconisStroock.Poincare.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:33.177979+00:00
-- url     : https://prove2.me/theorems/f8390958-5a3e-4071-8895-7269f0f8fad8
-- title:
--   Proposition 1 — β₁ ≤ 1 − 1/κ for reversible chains
-- statement:
--   Let $P$ be an irreducible transition matrix on a finite state space $X$ with at least two states, reversible with respect to its stationary probability distribution $\pi$. For every choice $\Gamma$ of one edge-simple path $\gamma_{xy}$ for each ordered pair $x\ne y$, let $\kappa(\Gamma)$ be the directed-edge congestion in (1.5). If $\beta_1$ is the second largest eigenvalue of $P$, then
--
--   $$
--   \beta_1\le 1-\frac{1}{\kappa(\Gamma)}.
--   $$
--
--   This is the paper's first geometric bound on a Markov chain eigenvalue: a path system with low congestion yields a quantitative spectral gap.
--
--   **Formalization Note** The hypothesis $|X|\ge2$ makes $\beta_1$ exist. The path system is universally quantified, as the paper says “for any choice of $\Gamma$.”
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 37, Proposition 1 and (1.5), https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_Poincare_Kappa

namespace DiaconisStroock.Poincare

open MarkovMixing

/-- Proposition 1 (Poincaré inequality), p. 37, with κ defined by (1.5). -/
theorem proposition_1 {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (hV : 2 ≤ Fintype.card V) (Γ : V → V → List V) (hΓ : IsPathSystem P π Γ) :
    lambdaTwo P ≤ 1 - 1 / kappa P π Γ := by sorry

end DiaconisStroock.Poincare
