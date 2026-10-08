-- Prove2me | Theorems.Thm_CompOT_EntropicDual_remark_4_21_gradients
-- name    : CompOT.EntropicDual.remark_4_21_gradients
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:10.546725+00:00
-- url     : https://prove2.me/theorems/e66a8ebc-7d0d-4573-8f07-6b47274055b2
-- title:
--   Remark 4.21, (4.33)–(4.34) — coordinate gradients of the entropic dual
-- statement:
--   For probability histograms $a\in\Sigma_n$, $b\in\Sigma_m$, a cost matrix $C$, and $\varepsilon>0$, let $Q(f,g)$ be the entropic dual objective. At any potentials $f\in\mathbb R^n$ and $g\in\mathbb R^m$, its partial derivatives are
--
--   $$
--   \frac{\partial Q}{\partial f_i}=a_i-e^{f_i/\varepsilon}\sum_j K_{ij}e^{g_j/\varepsilon},\qquad
--   \frac{\partial Q}{\partial g_j}=b_j-e^{g_j/\varepsilon}\sum_i K_{ij}e^{f_i/\varepsilon}.
--   $$
--
--   These formulas identify the row and column marginal errors of the scaled Gibbs matrix and underlie the log-domain updates.
--
--   **Formalization Note** Each partial derivative is a one-variable `HasDerivAt` statement obtained by changing one coordinate with `Function.update`.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Remark 4.21, (4.33)–(4.34), p. 449. https://doi.org/10.1561/2200000073

import Mathlib
import Definitions.Def_CompOT_EntropicDual_Defs

namespace CompOT.EntropicDual

/-- Remark 4.21, (4.33)–(4.34), p. 449: the two partial gradients of
the entropic dual objective, stated coordinatewise. -/
theorem remark_4_21_gradients {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f : Fin n → ℝ) (g : Fin m → ℝ) :
    (∀ i, HasDerivAt
      (fun t : ℝ => dualObjEnt C a b ε (Function.update f i t) g)
      (a i - Real.exp (f i / ε) *
        ∑ j, gibbs C ε i j * Real.exp (g j / ε)) (f i)) ∧
    (∀ j, HasDerivAt
      (fun t : ℝ => dualObjEnt C a b ε f (Function.update g j t))
      (b j - Real.exp (g j / ε) *
        ∑ i, gibbs C ε i j * Real.exp (f i / ε)) (g j)) := by sorry

end CompOT.EntropicDual
