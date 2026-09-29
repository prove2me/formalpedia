-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isFactorizableTestFn_principalLevel_tendsto_rightConv
-- name    : AutomorphicForm.exists_isFactorizableTestFn_principalLevel_tendsto_rightConv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/7d853f11-50fe-51cc-8cbe-cf1630786a3c
-- title:
--   Approximate identity by factorizable test functions at principal level
-- statement:
--   Let $K$ be a number field with ring of integers $\mathcal{O}=\mathcal{O}_K$, and let $N$ be a nonzero ideal of $\mathcal{O}$. The assertion is the existence of a sequence $f : \mathbb{N} \to (\mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C})$ with four properties. First, each $f_n$ satisfies `IsFactorizableTestFn`: there are $f_{n,\infty}$ on $\mathrm{GL}_2(\mathbb{A}_{K,\infty})$ and $f_{n,\mathrm{fin}}$ on $\mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}})$ with $f_{n,\infty}$ of the form $\Phi \circ \mathrm{archEntries}$ for a $C^\infty$ function $\Phi$ on matrices over the mixed space of $K$ and of compact support, $f_{n,\mathrm{fin}}$ locally constant of compact support, and $f_n(g)=f_{n,\infty}(\mathrm{glArch}\,g)\cdot f_{n,\mathrm{fin}}(\mathrm{glFin}\,g)$ for all $g$. Second, whenever $f_n(x)\neq 0$ one may write $x=ak$ with $\mathrm{glFin}\,a=1$ and $k$ in `principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K`, i.e. $k$ has trivial archimedean component (lies in the kernel of $\mathrm{glArch}$) and lies in the intersection of `levelOne (𝓞 K) K N` — the preimage under $\mathrm{glFin}$ of the level-$N$ subgroup `finiteLevelOne` of $\mathrm{GL}_2(\mathbb{A}_K^{\mathrm{fin}})$ — with its conjugate by the Weyl element $\begin{pmatrix}0&1\\1&0\end{pmatrix}$. Third, each $f_n$ is invariant under conjugation by the image under `rowIsometryInclAt₀` of any element of `rowIsometrySubgroup₀ w.Completion`, for every infinite place $w$ of $K$. Fourth, for every continuous $\varphi : \mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ with $\varphi(gk)=\varphi(g)$ for all $g$ and all $k$ in that same subgroup, and every $g$, the right convolutions $\mathrm{rightConv}\,\varphi\,f_n\,(g)=\int \varphi(gx)f_n(x)\,d\mu(x)$, taken against the adelic Haar measure `adelicGLHaar` on $\mathrm{GL}_2(\mathbb{A}_K)$, converge to $\varphi(g)$ as $n\to\infty$.
--
--   This provides an approximate identity on $\mathrm{GL}_2$ over the adeles, adapted to a principal congruence level and to conjugation-invariance under the isometry groups at the infinite places, in the style of the smoothing arguments used for automorphic forms on $\mathrm{GL}_2$. It is used in the analysis of isotypic cusp spaces at principal level, being cited by [`AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_isFundamentalDomain`](thm.html#AutomorphicForm.finiteDimensional_isotypicCuspSubmodule_principal_inf_archCutSubmodule_of_isFundamentalDomain) and by [`AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_le_of_isFundamentalDomain_of_pos`](thm.html#AutomorphicForm.isotypicCuspSubmodule_inf_archCutSubmodule_principalLevel_le_of_isFundamentalDomain_of_pos).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isFactorizableTestFn_principalLevel_tendsto_rightConv.lean

import Definitions.Def_AutomorphicForm_FactorizableTestFn
import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_PrincipalLevel

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel

theorem AutomorphicForm.exists_isFactorizableTestFn_principalLevel_tendsto_rightConv
    (K : Type) [Field K] [NumberField K] (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) :
    ∃ f : ℕ → (AdelicGL2 (𝓞 K) K → ℂ),
      (∀ n, IsFactorizableTestFn K (f n)) ∧
      (∀ n (x : AdelicGL2 (𝓞 K) K), f n x ≠ 0 →
        ∃ a k : AdelicGL2 (𝓞 K) K, glFin (𝓞 K) K a = 1 ∧
          k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K ∧ x = a * k) ∧
      (∀ n (w : InfinitePlace K) (k : rowIsometrySubgroup₀ w.Completion) (y : AdelicGL2 (𝓞 K) K),
        f n (rowIsometryInclAt₀ K w k * y * (rowIsometryInclAt₀ K w k)⁻¹) = f n y) ∧
      ∀ φ : AdelicGL2 (𝓞 K) K → ℂ, Continuous φ →
        (∀ g : AdelicGL2 (𝓞 K) K, ∀ k ∈ principalLevel (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K,
          φ (g * k) = φ g) →
        ∀ g : AdelicGL2 (𝓞 K) K,
          Filter.Tendsto (fun n => rightConv K φ (f n) g) Filter.atTop (nhds (φ g)) := by sorry
