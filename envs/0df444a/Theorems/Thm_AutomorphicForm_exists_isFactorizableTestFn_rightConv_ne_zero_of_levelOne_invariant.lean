-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
-- name    : AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/478723fd-46a3-5779-b468-c46f46973079
-- title:
--   Non-vanishing right convolution with a level-N factorisable test function
-- statement:
--   Let $K$ be a number field, $N$ a non-zero ideal of $\mathcal{O}_K$, and let $U$ denote the intersection of the subgroup `levelOne (𝓞 K) K N` of $\mathrm{GL}_2(\mathbb{A}_K)$ — the preimage under the finite-component map `glFin` of the group of those $g \in \mathrm{GL}_2(\mathbb{A}_K^{\mathrm{f}})$ for which both the matrix of $g$ and that of $g^{-1}$ satisfy the level-$N$ predicate `IsLevelOneMatrix` — with `finiteAdelicGL2Subgroup K`, the kernel of the archimedean-component map `glArch`, i.e. the elements whose archimedean component is $1$. Suppose $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ is continuous, does not vanish identically, and satisfies $\varphi(gk) = \varphi(g)$ for all $g$ and all $k \in U$. Then there exists $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ with the following four properties. First, $f$ is a factorisable test function: $f(g) = f_\infty(\mathrm{gl}_\infty(g)) \cdot f_{\mathrm{f}}(\mathrm{gl}_{\mathrm{f}}(g))$ where $f_\infty$ on $\mathrm{GL}_2(K_\infty)$ has compact support and is given by a $C^\infty$ function of the archimedean matrix entries (via `archEntries`), and $f_{\mathrm{f}}$ on $\mathrm{GL}_2(\mathbb{A}_K^{\mathrm{f}})$ is locally constant with compact support. Second, $f(kx) = f(x)$ for all $k \in U$ and all $x$. Third, $f$ vanishes off $\{a k\}$ with $a$ of finite component $1$ and $k \in U$: if $f(x) \neq 0$ then $x = ak$ for some such $a$, $k$. Fourth, there is a $g$ with $(\varphi * f)(g) = \int \varphi(gx) f(x)\,dx \neq 0$, the integral being the Bochner integral against the Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$ for its Borel structure.
--
--   This is the standard device of smoothing an automorphic-type function by right convolution with a Hecke-algebra element: a level-$N$ test function, factorised into a smooth compactly supported archimedean factor and a locally constant compactly supported finite factor, can be chosen so that the convolution is not identically zero while retaining the level-$N$ invariance and support constraints. It is used in the analysis of class sums and archimedean weights for adelic $\mathrm{GL}_2$, being cited among others by the class-sum growth estimates and by the construction of archimedean weight characters occurring in a class.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicLevel

theorem AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_levelOne_invariant
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * k) = φ g) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧
      (∀ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (k * x) = f x) ∧
      (∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
        glFin (𝓞 K) K a = 1 ∧ k ∈ levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by sorry
