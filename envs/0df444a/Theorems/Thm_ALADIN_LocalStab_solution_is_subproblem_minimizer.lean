-- Prove2me | Theorems.Thm_ALADIN_LocalStab_solution_is_subproblem_minimizer
-- name    : ALADIN.LocalStab.solution_is_subproblem_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:21.729003+00:00
-- url     : https://prove2.me/theorems/5af0d668-a518-4b17-b523-eff5b8f3ef43
-- title:
--   §7, proof of Lemma 3 — $\xi_i(x^*,\lambda^*)=x^*_i$: $x^*_i$ is a KKT point and strict local minimizer of (7.1)
-- statement:
--   Let problem (1.1) be given with $f_i,h_i$ twice continuously differentiable, let $(x^*,\lambda^*,\kappa)$ be a regular KKT point of (1.1), let $\Sigma_i$ be symmetric positive semidefinite, $\rho>0$, and assume
--
--   $$
--   \nabla^2\big[f_i+\kappa_i^\top h_i\big](x^*_i) + \rho\,\Sigma_i \succ 0\qquad (i=1,\dots,N).
--   $$
--
--   Then for every block $i$, the decoupled problem (7.1) with parameters $(x,\lambda)=(x^*,\lambda^*)$,
--   $$
--   \min_{\xi}\ f_i(\xi) + \lambda^{*\top} A_i\xi + \tfrac{\rho}{2}\|\xi-x^*_i\|^2_{\Sigma_i}\quad\text{s.t.}\quad h_i(\xi)\le 0,
--   $$
--   satisfies:
--
--   1. $x^*_i$ is a stationary point with multiplier $\kappa_i$: $\nabla_\xi\varphi_i(x^*,\lambda^*;x^*_i) + \sum_j\kappa_{ij}\nabla h_{ij}(x^*_i)=0$;
--   2. $x^*_i$ is feasible, $h_i(x^*_i)\le 0$;
--   3. $x^*_i$ is a strict local minimizer: there is $r>0$ with $\varphi_i(x^*,\lambda^*;x^*_i)<\varphi_i(x^*,\lambda^*;\xi)$ for every feasible $\xi\neq x^*_i$ with $\|\xi-x^*_i\|<r$.
--
--   This is the step "$\xi_i(x^*,\lambda^*)=x^*_i$" of the proof of Lemma 3: at the solution, the decoupled problems return the solution itself. The paper derives it from the first-order KKT conditions of (7.1); together with the Hessian hypothesis it identifies $x^*_i$ as the isolated local minimizer around which the parametric minimizer is built.
--
--   **Formalization Note** Stationarity is stated for every direction $d$ through Fréchet derivatives. Norms are Mathlib's sup norms.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1117, §7, proof of Lemma 3 (ξi(x*, λ*) = x*_i, from the first order KKT conditions of (7.1))

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Problem
import Definitions.Def_ALADIN_LocalStab_Decoupled

open Matrix

namespace ALADIN.LocalStab

/-- §7, proof of Lemma 3, p. 1117: `ξᵢ(x*, λ*) = x*ᵢ`, from the first-order KKT conditions of (7.1).
Let `(x*, λ*, κ)` be a regular KKT point of (1.1), `fᵢ`, `hᵢ` `C²`, `Σᵢ ⪰ 0`, `ρ > 0`, and
`∇²[fᵢ + κᵢᵀhᵢ](x*ᵢ) + ρΣᵢ ≻ 0`. Then for every block `i`, at the parameters `(x, λ) = (x*, λ*)`:
1. `x*ᵢ` satisfies the stationarity condition of (7.1) with multiplier `κᵢ`
   (the gradient of the proximal term vanishes at `ξ = xᵢ = x*ᵢ`);
2. `x*ᵢ` is a strict local minimizer of (7.1). -/
theorem solution_is_subproblem_minimizer {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (hSig : ∀ i, (Sig i).PosSemidef)
    (xs : Fin N → Fin n → ℝ) (lamS : Fin m → ℝ) (κ : Fin N → Fin nh → ℝ)
    (hreg : P.IsRegularKKTPoint xs lamS κ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ i (d : Fin n → ℝ), d ≠ 0 →
      0 < hessQuad (P.lagBlock i (κ i)) (xs i) d + ρ * (d ⬝ᵥ (Sig i *ᵥ d))) :
    ∀ i,
      (∀ d : Fin n → ℝ, fderiv ℝ (decoupledObjective P ρ Sig xs lamS i) (xs i) d
          + ∑ j, κ i j * fderiv ℝ (fun ξ => P.h i ξ j) (xs i) d = 0) ∧
      xs i ∈ decoupledFeasibleSet P i ∧
      ∃ r > 0, ∀ ξ ∈ decoupledFeasibleSet P i, ‖ξ - xs i‖ < r → ξ ≠ xs i →
        decoupledObjective P ρ Sig xs lamS i (xs i) < decoupledObjective P ρ Sig xs lamS i ξ := by sorry

end ALADIN.LocalStab
