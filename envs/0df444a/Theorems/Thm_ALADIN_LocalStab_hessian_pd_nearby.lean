-- Prove2me | Theorems.Thm_ALADIN_LocalStab_hessian_pd_nearby
-- name    : ALADIN.LocalStab.hessian_pd_nearby
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:28.389272+00:00
-- url     : https://prove2.me/theorems/c521eac0-be0f-4887-9b58-2b698929301e
-- title:
--   §7, proof of Lemma 3 — the Hessians $\nabla^2[f_i+\kappa^\top h_i]+\rho\Sigma_i$ stay positive definite near $(x^*_i,\kappa_i)$
-- statement:
--   Let problem (1.1) be given with $f_i$ and $h_i$ twice continuously differentiable, let $\Sigma_i\in\mathbb R^{n\times n}$, $\rho\in\mathbb R$, $x^*\in\mathbb R^{Nn}$ and $\kappa_i\in\mathbb R^{n_h}$ ($i=1,\dots,N$), and assume that for every block $i$
--
--   $$
--   \nabla^2\big[f_i+\kappa_i^\top h_i\big](x^*_i) + \rho\,\Sigma_i \succ 0,
--   $$
--
--   in the sense that $d^\top\nabla^2[f_i+\kappa_i^\top h_i](x^*_i)d + \rho\, d^\top\Sigma_id>0$ for every $d\ne 0$. Then there is $\delta>0$ such that for every block $i$, every $\xi\in\mathbb R^n$ with $\|\xi-x^*_i\|<\delta$ and every $\kappa'\in\mathbb R^{n_h}$ with $\|\kappa'-\kappa_i\|<\delta$,
--
--   $$
--   d^\top\nabla^2\big[f_i+\kappa'^\top h_i\big](\xi)\,d + \rho\, d^\top\Sigma_i d \;>\;0 \qquad\text{for every } d\ne 0 .
--   $$
--
--   In the proof of Lemma 3 this is the first step: the Hessian of the Lagrangian of each decoupled problem (7.1) remains strictly positive definite at primal–dual points near the solution, which is what makes the parametric minimizers well defined.
--
--   **Formalization Note** The page writes the Hessian evaluated at $x^*_i$ and asserts it is positive "for all $(x,\lambda)$ in a small neighborhood of $(x^*,\lambda^*)$"; the matrix printed does not depend on $(x,\lambda)$, and the content the proof needs is positivity of the Hessian of the Lagrangian of (7.1) at nearby points $\xi$ with nearby multipliers $\kappa'$, which is what is stated here. Norms are Mathlib's sup norms on `Fin n → ℝ` and `Fin nh → ℝ`; $d^\top\nabla^2 g(z) d$ is `hessQuad g z d`.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1117, §7, proof of Lemma 3, first sentence (Hessians of (7.1) strictly positive near (x*, λ*))

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Problem
import Definitions.Def_ALADIN_LocalStab_Decoupled

open Matrix

namespace ALADIN.LocalStab

/-- §7, proof of Lemma 3, p. 1117: the Hessians of the decoupled problems (7.1) stay positive
definite near the solution. If `fᵢ`, `hᵢ` are `C²` and `∇²[fᵢ + κᵢᵀhᵢ](x*ᵢ) + ρΣᵢ ≻ 0` for every
block, then there is `δ > 0` such that `∇²[fᵢ + κ'ᵀhᵢ](ξ) + ρΣᵢ ≻ 0` for every block `i`, every
`ξ` with `‖ξ − x*ᵢ‖ < δ` and every multiplier `κ'` with `‖κ' − κᵢ‖ < δ`. -/
theorem hessian_pd_nearby {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (ρ : ℝ)
    (xs : Fin N → Fin n → ℝ) (κ : Fin N → Fin nh → ℝ)
    (hHess : ∀ i (d : Fin n → ℝ), d ≠ 0 →
      0 < hessQuad (P.lagBlock i (κ i)) (xs i) d + ρ * (d ⬝ᵥ (Sig i *ᵥ d))) :
    ∃ δ > 0, ∀ i (ξ : Fin n → ℝ) (κ' : Fin nh → ℝ), ‖ξ - xs i‖ < δ → ‖κ' - κ i‖ < δ →
      ∀ d : Fin n → ℝ, d ≠ 0 →
        0 < hessQuad (P.lagBlock i κ') ξ d + ρ * (d ⬝ᵥ (Sig i *ᵥ d)) := by sorry

end ALADIN.LocalStab
