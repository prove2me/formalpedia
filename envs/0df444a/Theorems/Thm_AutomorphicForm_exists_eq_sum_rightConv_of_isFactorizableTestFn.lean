-- Prove2me | Theorems.Thm_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn
-- name    : AutomorphicForm.exists_eq_sum_rightConv_of_isFactorizableTestFn
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:53.89515+00:00
-- url     : https://prove2.me/theorems/456dce32-e72d-5a1e-87f8-d331c1b4808a
-- title:
--   Factorizable test functions as finite sums of convolutions
-- statement:
--   Let $K$ be a number field and let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be a factorizable test function, that is: there are functions $f_\infty$ on $\mathrm{GL}_2(K \otimes \mathbb{R})$ and $f_{\mathrm{fin}}$ on $\mathrm{GL}_2$ of the finite adèles of $\mathcal{O}_K$ in $K$ such that $f_\infty$ is given by $f_\infty(g) = \Phi(\mathrm{archEntries}\,K\,g)$ for some $\Phi$ on the $2 \times 2$ matrices over the mixed space of $K$ which is $C^\infty$ over $\mathbb{R}$, $f_\infty$ has compact support, $f_{\mathrm{fin}}$ is locally constant with compact support, and $f(g) = f_\infty(\mathrm{glArch}\,g) \cdot f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ for all $g$, where $\mathrm{glArch}$ and $\mathrm{glFin}$ are the maps on $\mathrm{GL}_2$ induced by the archimedean and finite projections of the adèle ring. Then there exist $n \in \mathbb{N}$ and two families $g_1,\dots,g_n$ and $h_1,\dots,h_n$ of functions $\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$, each $g_k$ and each $h_k$ again a factorizable test function in the above sense, such that for every $x \in \mathrm{GL}_2(\mathbb{A}_K)$,
--   $$f(x) = \sum_{k=1}^{n} \int g_k(xy)\, h_k(y^{-1})\, d\mu(y),$$
--   the integral being `rightConv` of $g_k$ against $y \mapsto h_k(y^{-1})$, taken against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ with its Borel measurable structure.
--
--   This is the Dixmier–Malliavin factorisation in the adelic setting: the space of factorizable test functions on $\mathrm{GL}_2(\mathbb{A}_K)$ coincides with its own convolution square, the archimedean factor being split by the smooth factorisation theorem and the finite factor absorbing an indicator of a small compact open subgroup. It is used in the analysis of the convolution operators attached to test functions, in particular in the estimates for orthonormal families of cusp forms of a given level.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_eq_sum_rightConv_of_isFactorizableTestFn.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_RightConvolution

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField AutomorphicForm

theorem AutomorphicForm.exists_eq_sum_rightConv_of_isFactorizableTestFn (K : Type) [Field K] [NumberField K]
    (f : GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ) (hf : IsFactorizableTestFn K f) :
    ∃ n : ℕ, ∃ g h : Fin n → GL (Fin 2) (AdeleRing (𝓞 K) K) → ℂ,
      (∀ k, IsFactorizableTestFn K (g k)) ∧ (∀ k, IsFactorizableTestFn K (h k)) ∧
        ∀ x : GL (Fin 2) (AdeleRing (𝓞 K) K), f x = ∑ k, rightConv K (g k) (fun y => h k y⁻¹) x := by sorry
