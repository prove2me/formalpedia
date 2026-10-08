-- Prove2me | Theorems.Thm_ALADIN_LocalStab_parametric_minimizer
-- name    : ALADIN.LocalStab.parametric_minimizer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:29.600634+00:00
-- url     : https://prove2.me/theorems/ef9f6c9c-43be-4c1d-85c2-abac51fbf1ab
-- title:
--   §7, proof of Lemma 3 — the parametric minimizers $\xi_i(x,\lambda)$ of (7.1) are locally well defined, locally unique and $C^1$
-- statement:
--   Assume the hypotheses of Lemma 3: $f_i,h_i$ are twice continuously differentiable, $x^*$ is a local minimizer of (1.1) and $(x^*,\lambda^*,\kappa)$ is a regular KKT point, $\Sigma_i$ is symmetric positive semidefinite, $\rho>0$, and
--   $$
--   \nabla^2\big[f_i+\kappa_i^\top h_i\big](x^*_i) + \rho\,\Sigma_i \succ 0\qquad (i=1,\dots,N).
--   $$
--
--   Then there exist a radius $r>0$, an open neighbourhood $U\subseteq\mathbb R^{Nn}\times\mathbb R^m$ of $(x^*,\lambda^*)$, and maps $\xi_i:\mathbb R^{Nn}\times\mathbb R^m\to\mathbb R^n$ ($i=1,\dots,N$), continuously differentiable on $U$, with $\xi_i(x^*,\lambda^*)=x^*_i$, such that for every $(x,\lambda)\in U$ and every block $i$:
--
--   1. $\xi_i(x,\lambda)$ is a local minimizer of the decoupled problem (7.1) with parameters $(x,\lambda)$;
--   2. $\|\xi_i(x,\lambda)-x^*_i\|<r$;
--   3. every local minimizer $\eta$ of that problem with $\|\eta - x^*_i\|<r$ equals $\xi_i(x,\lambda)$.
--
--   This is the central step of the proof of Lemma 3 ("the parametric minimizers $\xi_i(x,\lambda)$ are locally well-defined and continuously differentiable functions in this neighborhood, because $(x^*,\lambda^*)$ is assumed to be a regular KKT point"): it turns the decoupled problems into a smooth map of the ALADIN iterates near a solution.
--
--   **Formalization Note** "Locally well-defined" is rendered as existence plus uniqueness of the local minimizer within the fixed radius $r$ of $x^*_i$, uniformly for $(x,\lambda)\in U$. $U$ is a subset of the product space `(Fin N → Fin n → ℝ) × (Fin m → ℝ)`; norms are Mathlib's sup norms. A local minimizer is required to be feasible.
-- source:
--   Houska, Frasch, Diehl, An augmented Lagrangian based algorithm for distributed nonconvex optimization, SIAM J. Optim. 26 (2016), p. 1117, §7, proof of Lemma 3 (parametric minimizers ξi(x, λ) locally well-defined and continuously differentiable)

import Mathlib
import Definitions.Def_ALADIN_LocalStab_Problem
import Definitions.Def_ALADIN_LocalStab_Decoupled

open Matrix

namespace ALADIN.LocalStab

/-- §7, proof of Lemma 3, p. 1117: the parametric minimizers `ξᵢ(x, λ)` of (7.1) are locally
well defined and continuously differentiable. Under the hypotheses of Lemma 3 there are a radius
`r > 0`, an open neighbourhood `U` of `(x*, λ*)` and maps `ξᵢ`, `C¹` on `U`, with
`ξᵢ(x*, λ*) = x*ᵢ`, such that for every `(x, λ) ∈ U` the point `ξᵢ(x, λ)` is a local minimizer of
(7.1) with parameters `(x, λ)`, lies within `r` of `x*ᵢ`, and is the only local minimizer of (7.1)
within `r` of `x*ᵢ`. -/
theorem parametric_minimizer {N n m nh : ℕ} (P : Problem N n m nh)
    (hf : ∀ i, ContDiff ℝ 2 (P.f i)) (hh : ∀ i, ContDiff ℝ 2 (P.h i))
    (Sig : Fin N → Matrix (Fin n) (Fin n) ℝ) (hSig : ∀ i, (Sig i).PosSemidef)
    (xs : Fin N → Fin n → ℝ) (lamS : Fin m → ℝ) (κ : Fin N → Fin nh → ℝ)
    (hmin : P.IsLocalMinimizer xs)
    (hreg : P.IsRegularKKTPoint xs lamS κ)
    (ρ : ℝ) (hρ : 0 < ρ)
    (hHess : ∀ i (d : Fin n → ℝ), d ≠ 0 →
      0 < hessQuad (P.lagBlock i (κ i)) (xs i) d + ρ * (d ⬝ᵥ (Sig i *ᵥ d))) :
    ∃ r > 0, ∃ U : Set ((Fin N → Fin n → ℝ) × (Fin m → ℝ)), IsOpen U ∧ (xs, lamS) ∈ U ∧
      ∃ ξ : Fin N → (Fin N → Fin n → ℝ) × (Fin m → ℝ) → Fin n → ℝ, ∀ i,
        ContDiffOn ℝ 1 (ξ i) U ∧ ξ i (xs, lamS) = xs i ∧
        ∀ p ∈ U,
          IsDecoupledLocalMin P ρ Sig p.1 p.2 i (ξ i p) ∧
          ‖ξ i p - xs i‖ < r ∧
          ∀ η : Fin n → ℝ,
            IsDecoupledLocalMin P ρ Sig p.1 p.2 i η →
            ‖η - xs i‖ < r → η = ξ i p := by sorry

end ALADIN.LocalStab
