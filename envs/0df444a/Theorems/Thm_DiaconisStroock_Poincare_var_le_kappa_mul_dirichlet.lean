-- Prove2me | Theorems.Thm_DiaconisStroock_Poincare_var_le_kappa_mul_dirichlet
-- name    : DiaconisStroock.Poincare.var_le_kappa_mul_dirichlet
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:05:51.630049+00:00
-- url     : https://prove2.me/theorems/30e17a00-cdd3-4b18-84ed-fa7d467bc8b6
-- title:
--   §1B, proof of Proposition 1 — variance bounded by κ times Dirichlet energy
-- statement:
--   Let $P$ be an irreducible stochastic transition matrix on a finite state space, reversible with respect to a stationary probability distribution $\pi$. Choose an edge-simple path $\gamma_{xy}$ for each ordered pair of distinct states, and let $\kappa(\Gamma)$ be the directed-edge congestion in (1.5). Then every real function $\phi$ satisfies
--
--   $$
--   \operatorname{Var}_\pi(\phi)\le\kappa(\Gamma)\,\mathcal E_P(\phi,\phi),
--   $$
--
--   where $\mathcal E_P(\phi,\phi)=\frac12\sum_{x,y}(\phi(x)-\phi(y))^2Q(x,y)$. This functional inequality is the step immediately before the spectral conclusion of Proposition 1.
--
--   **Formalization Note** The valid path system excludes repeated unordered edges. The statement also covers a one-state chain, for which both sides are zero.
-- source:
--   Diaconis and Stroock, Geometric bounds for eigenvalues of Markov chains, Ann. Appl. Probab. 1 (1991), p. 38, §1B, proof of Proposition 1, final display, https://doi.org/10.1214/aoap/1177005980

import Mathlib
import Definitions.Def_mm_spectral
import Definitions.Def_DiaconisStroock_Poincare_Kappa

namespace DiaconisStroock.Poincare

open MarkovMixing

/-- The Poincaré inequality reached in the proof of Proposition 1, p. 38. -/
theorem var_le_kappa_mul_dirichlet {V : Type*} [Fintype V] [DecidableEq V]
    (P : Matrix V V ℝ) (hP : IsStochastic P) (hirr : MarkovMixing.Irreducible P)
    (π : V → ℝ) (hπ : IsStationary P π) (hrev : DetailedBalance P π)
    (Γ : V → V → List V) (hΓ : IsPathSystem P π Γ) (φ : V → ℝ) :
    distVar π φ ≤ kappa P π Γ * dirichletForm P π φ := by sorry

end DiaconisStroock.Poincare
