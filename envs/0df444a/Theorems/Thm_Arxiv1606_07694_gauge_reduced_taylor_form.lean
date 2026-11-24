-- Prove2me | Theorems.Thm_Arxiv1606_07694_gauge_reduced_taylor_form
-- name    : Arxiv1606_07694.gauge_reduced_taylor_form
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T23:25:40.62418+00:00
-- url     : https://prove2.me/theorems/814bf5c5-4aeb-454f-9cb1-471b4088fdbe
-- title:
--   Eqs. (16)-(19): the terms $B^{(n)}$ and $C^{(n)}$ can be removed by a term vanishing on $\mathcal P^{(n)}$
-- statement:
--   Let $n\ge0$, fix $\mathbf k,\mathbf k_0\in\mathbb R^2$, and let $g$ be a symmetric complex function of $(\mathbf k_1,\dots,\mathbf k_n)\in(\mathbb R^2)^n$ with the second-order expansion (16)
--   $$g=A+B_\mu\textstyle\sum_i\mathbf k_i^\mu+C_{\mu\nu}\sum_i\mathbf k_i^\mu\mathbf k_i^\nu-D_{\mu\nu}\sum_{i<j}\mathbf k_i^\mu\mathbf k_j^\nu+o(k^2).$$
--   Then there are coefficients $\hat A_\mu$, $\hat B_{\mu\nu}$ such that the function
--   $$f=(\mathbf k_1+\dots+\mathbf k_n+\mathbf k_0-\mathbf k)^\mu\big(\hat A_\mu+\hat B_{\mu\nu}(\mathbf k_1+\dots+\mathbf k_n)^\nu\big)$$
--   vanishes on $\mathcal P^{(n)}$ and $g+f$ has an expansion without the $B$ and $C$ terms:
--   $$g+f=A'-D'_{\mu\nu}\textstyle\sum_{i<j}\mathbf k_i^\mu\mathbf k_j^\nu+o(k^2)\quad\text{for some }A',D'.\qquad(19)$$
--
--   Since $f$ vanishes on the hyperplane, where the kernel is defined, the kernels may be assumed to have the form (19) without loss of generality.
--
--   **Formalization Note** The coefficients $A'$ and $D'$ of (19) are in general not the $A$ and $D$ of (16), although the paper uses the same symbols. $D'$ differs from $D$ when $C\ne0$, and $A'$ differs from $A$ when $\mathbf k\ne\mathbf k_0$. The statement is therefore existential in $A',D'$.
-- source:
--   G. Bimonte, Wave-scattering from a gently curved surface, arXiv:1606.07694v1 (2016), claim c004; Section "Resummation of the perturbative series", eqs. (16)-(19), PDF p. 3

import Mathlib
import Definitions.Def_Arxiv1606_07694_Basic

open MeasureTheory Complex

namespace Arxiv1606_07694

theorem gauge_reduced_taylor_form {n : ℕ} (k k0 : Vec2) (g : (Fin n → Vec2) → ℂ)
    (hg : ∀ (κ : Fin n → Vec2) (σ : Equiv.Perm (Fin n)), g (κ ∘ σ) = g κ)
    (a : ℂ) (b : Fin 2 → ℂ) (C Dm : Matrix (Fin 2) (Fin 2) ℂ)
    (h16 : HasSecondOrderExpansion g a b C Dm) :
    ∃ (Ahat : Fin 2 → ℂ) (Bhat : Matrix (Fin 2) (Fin 2) ℂ),
      (∀ κ : Fin n → Vec2, OnHyperplane k k0 κ → gaugeTerm k k0 Ahat Bhat κ = 0) ∧
      ∃ (a' : ℂ) (Dm' : Matrix (Fin 2) (Fin 2) ℂ),
        HasReducedExpansion (fun κ => g κ + gaugeTerm k k0 Ahat Bhat κ) a' Dm' := by sorry

end Arxiv1606_07694
