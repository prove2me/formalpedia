-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_principalLevel_invariant
-- name    : AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_principalLevel_invariant
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/d4c1c01e-25f9-5c6b-b47e-a79f0e98531c
-- title:
--   Nonzero convolution against a factorizable test function at level N
-- statement:
--   Let $K$ be a number field, $N$ a non-zero ideal of $\mathcal{O}_K$, and let $\varphi : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous and not identically zero (there is a $g$ with $\varphi(g)\neq 0$), where $\mathrm{GL}_2(\mathbb{A}_K)$ denotes the general linear group of $2\times 2$ matrices over the adele ring of $K$. Write $U_N$ for the subgroup $\mathrm{principalLevel}(\mathcal{O}_K,K,N) \sqcap \mathrm{finiteAdelicGL2Subgroup}(K)$: here $\mathrm{principalLevel}$ is the intersection of $\mathrm{levelOne}(\mathcal{O}_K,K,N)$, the preimage under $\mathrm{glFin}$ of the subgroup $\mathrm{finiteLevelOne}(\mathcal{O}_K,K,N)$ of $\mathrm{GL}_2$ over the finite adeles, with its conjugate by the Weyl element $\bigl(\begin{smallmatrix}0&1\\1&0\end{smallmatrix}\bigr)$, and $\mathrm{finiteAdelicGL2Subgroup}(K)$ is the kernel of $\mathrm{glArch}$, i.e. the elements with trivial archimedean component. Assume $\varphi(gk)=\varphi(g)$ for all $g$ and all $k\in U_N$. The conclusion asserts the existence of $f : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with four properties: (i) $f$ is factorizable, $f(g)=f_\infty(\mathrm{glArch}\,g)\cdot f_{\mathrm{fin}}(\mathrm{glFin}\,g)$ where $f_\infty$ is compactly supported and of the form $\Phi\circ\mathrm{archEntries}$ for a $C^\infty$ function $\Phi$ of the matrix entries in the mixed space of $K$, and $f_{\mathrm{fin}}$ is locally constant with compact support; (ii) $f(kx)=f(x)$ for all $k\in U_N$ and all $x$; (iii) whenever $f(x)\neq 0$, one can write $x=ak$ with $\mathrm{glFin}\,a=1$ and $k\in U_N$; (iv) there is a $g$ with $\mathrm{rightConv}_K\,\varphi\,f\,(g)=\int \varphi(gx)f(x)\,dx \neq 0$, the integral being the Bochner integral against the Haar measure of $\mathrm{GL}_2(\mathbb{A}_K)$ for its Borel $\sigma$-algebra.
--
--   This is the standard statement that a non-zero continuous function on $\mathrm{GL}_2(\mathbb{A}_K)$ invariant under a congruence-type level subgroup is not annihilated by the Hecke algebra of smooth compactly supported test functions acting by right convolution, here with the test function chosen factorizable, left-invariant under the level subgroup and supported over it. It feeds the approximation estimate [`AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample_principal`](thm.html#AutomorphicForm.exists_setLIntegral_sub_sum_translate_sq_lt_of_agreesAwayFromFinite_of_coversModCentre_ample_principal), and the proof uses that factorizable test functions are continuous with compact support.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_rightConv_ne_zero_of_principalLevel_invariant.lean

import Definitions.Def_AutomorphicForm_RightConvolution
import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open NumberField NumberField.AdelicLevel

theorem AutomorphicForm.exists_isFactorizableTestFn_rightConv_ne_zero_of_principalLevel_invariant
    (K : Type) [Field K] [NumberField K]
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 K) K → ℂ) (hcont : Continuous φ) (hne : ∃ g, φ g ≠ 0)
    (hlev : ∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
      φ (g * k) = φ g) :
    ∃ f : AdelicGL2 (𝓞 K) K → ℂ,
      IsFactorizableTestFn K f ∧
      (∀ k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K, ∀ x, f (k * x) = f x) ∧
      (∀ x, f x ≠ 0 → ∃ a k : AdelicGL2 (𝓞 K) K,
        glFin (𝓞 K) K a = 1 ∧ k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) ∧
      ∃ g, rightConv K φ f g ≠ 0 := by sorry
