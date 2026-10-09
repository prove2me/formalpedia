-- Prove2me | Theorems.Thm_DurmusULA_StrongLC_proposition_2
-- name    : DurmusULA.StrongLC.proposition_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T14:17:26.294408+00:00
-- url     : https://prove2.me/theorems/7fb93305-9d0e-4dd4-89bd-f268d5dbfb82
-- title:
--   Proposition 2, p. 5 — under L1 and (3), the decomposition bound (10) for ‖δ_xQ^p_γ − π‖_TV
-- statement:
--   Let $U$ satisfy **L1** with constant $L$, let $\pi\propto e^{-U}$ and let $(P_t)_{t\ge0}$ be the semigroup of the Langevin diffusion $dY_t=-\nabla U(Y_t)dt+\sqrt2\,dB^d_t$. Let $(\gamma_k)_{k\ge1}$ be nonnegative step sizes, $x\in\mathbb R^d$ and $0\le n<p$. Suppose the geometric ergodicity (3) holds at the initial law $\mu_0=\delta_xQ^n_\gamma$: there are $\kappa\in[0,1)$ and $C<\infty$ with
--   $$\|\delta_xQ^n_\gamma P_t-\pi\|_{\mathrm{TV}}\le C\kappa^t\quad\text{for all }t>0,$$
--   and suppose $A(\gamma,x)=\sup_{k\ge0}\int\|\nabla U(z)\|^2\,Q^k_\gamma(x,dz)\le a<\infty$ (11). Then
--   $$\|\delta_xQ^p_\gamma-\pi\|_{\mathrm{TV}}\le 2^{-1/2}L\Big(\sum_{k=n}^{p-1}\Big\{\frac{\gamma_{k+1}^3}{3}a+d\gamma_{k+1}^2\Big\}\Big)^{1/2}+C\kappa^{\Gamma_{n+1,p}} .\qquad(10)$$
--
--   The first term is the discretisation error of $p-n$ Euler steps started from $\delta_xQ^n_\gamma$; the second is the convergence of the continuous diffusion over the time $\Gamma_{n+1,p}$.
--
--   **Formalization Note** (3) is assumed only at $\mu_0=\delta_xQ^n_\gamma$, the one instance the proof uses, with a finite constant $C$ standing for $C(\delta_xQ^n_\gamma)$ (if it is infinite, (10) is empty). The supremum $A(\gamma,x)$ enters through an upper bound $a$ on every $\int\|\nabla U\|^2d(\delta_xQ^k_\gamma)$, written as lower Lebesgue integrals. (11) prints $Q^k_\gamma(y,dz)$; the left side depends on $x$, so it is read with $x$. Steps are indexed from $k=1$.
-- source:
--   Durmus and Moulines, Non-asymptotic convergence analysis for the Unadjusted Langevin Algorithm, arXiv:1507.05021v3, p. 5, Proposition 2, (10), (11); (3) p. 4; L1 p. 3

import Mathlib
import Definitions.Def_DurmusULA_StrongLC_Model

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal RealInnerProductSpace

namespace DurmusULA.StrongLC

theorem proposition_2 (d : ℕ) (U : EthierKurtz.SDEState d → ℝ) (L : ℝ)
    (P : ℝ≥0 → EthierKurtz.SDEState d → Measure (EthierKurtz.SDEState d))
    (hL1 : L1 U L)
    (hP : IsDiffusionSemigroup (fun x => -gradient U x) (Real.sqrt 2) P)
    (κ : ℝ) (hκ : 0 ≤ κ ∧ κ < 1)
    (γ : ℕ → ℝ) (hγ : ∀ k, 1 ≤ k → 0 ≤ γ k)
    (x : EthierKurtz.SDEState d) (n p : ℕ) (hp : 1 ≤ p) (hnp : n < p)
    (C : ℝ)
    (hC : ∀ t : ℝ≥0, 0 < t →
      tvNorm ((ulaLaw U γ x n).bind (P t)) (gibbs U) ≤ C * κ ^ (t : ℝ))
    (a : ℝ)
    (hA : ∀ k : ℕ, ∫⁻ z, ENNReal.ofReal (‖gradient U z‖ ^ 2) ∂(ulaLaw U γ x k) ≤ ENNReal.ofReal a) :
    tvNorm (ulaLaw U γ x p) (gibbs U) ≤
      (Real.sqrt 2)⁻¹ * L *
          Real.sqrt (∑ k ∈ Finset.Ico n p, (γ (k + 1) ^ 3 / 3 * a + (d : ℝ) * γ (k + 1) ^ 2)) +
        C * κ ^ (Gam γ (n + 1) p) := by sorry

end DurmusULA.StrongLC
