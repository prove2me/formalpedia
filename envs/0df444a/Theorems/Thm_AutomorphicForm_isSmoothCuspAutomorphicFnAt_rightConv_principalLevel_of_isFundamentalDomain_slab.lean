-- Prove2me | Theorems.Thm_AutomorphicForm_isSmoothCuspAutomorphicFnAt_rightConv_principalLevel_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.isSmoothCuspAutomorphicFnAt_rightConv_principalLevel_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/647aa24f-d7c0-5f42-a9f2-535f6d779d20
-- title:
--   Right convolution preserves cusp forms and produces smoothness
-- statement:
--   Let $L$ be a number field, $\alpha,\beta$ real numbers and $\Phi_L$ a subset of $\mathrm{GL}_2(\mathbb{A}_L)$ (the general linear group of degree $2$ over the adele ring of $L$) contained in the slab $\{g : \|\det g\| \in [\alpha,\beta]\}$, where $\|\cdot\|$ is the idele norm given by the value of the distributive Haar character on $\mathbb{A}_L$, and assume $\Phi_L$ is a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain`, for the action of the image of $\mathrm{GL}_2(L)$ under `globalPoints` on the restriction of the adelic Haar measure `adelicGLHaar` to that slab. Fix a homomorphism $\xi_L$ from the full unit group of $\mathbb{A}_L$ (as the subgroup $\top$) to $\mathbb{C}^\times$, a nonzero ideal $N$ of $\mathcal{O}_L$, and a continuous compactly supported $\varphi : \mathrm{GL}_2(\mathbb{A}_L) \to \mathbb{C}$ invariant under left translation by the group $K(N) := \mathrm{principalLevel}(N) \cap \ker(\mathrm{glArch})$, the intersection of `levelOne` at $N$ with its conjugate by the Weyl element, cut down to elements with trivial archimedean component. Let $v$ be continuous and satisfy `IsCuspAutomorphicFnAt` for the data packaged by `productionPinsOf` from the Borel structure and Haar measure on $\mathrm{GL}_2(\mathbb{A}_L)$, the set $\Phi_L$, the central subgroup $\top$, the level family $M \mapsto K(M)$, the Hecke elements `heckeGen`, and the conditional measure of the adelic additive Haar measure on `adelicBox`; that is, $v$ satisfies `LsXiMemberAt` for $\xi_L$ and $\Phi_L$ and is `IsCuspidalFn` along $x \mapsto \begin{pmatrix}1&x\\0&1\end{pmatrix}$ for that conditional measure. Then the right convolution $g \mapsto \int v(gx)\varphi(x)\,dx$ against `adelicGLHaar` satisfies `IsSmoothCuspAutomorphicFnAt` for the same pins and $\xi_L$ (i.e. is again such a cusp form and is `IsKfSmooth`), is continuous, and is invariant under right translation by every $u \in K(N)$.
--
--   This is the stability of the space of cusp forms under the smoothing operators $R(\varphi)$, in the variant where the level family consists of the principal congruence subgroups $K(M)$ cut down to the finite adeles and cuspidality is read on an exact fundamental domain for the determinant slab. It is used to pass from continuous cusp forms to forms of a definite level that are smooth under the finite adeles, and feeds the construction of isotypic cusp forms obtained by convolving with bi-invariant test functions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isSmoothCuspAutomorphicFnAt_rightConv_principalLevel_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_UnitFactorizableOfType
import Definitions.Def_NumberField_PrincipalLevel
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar NumberField.AdelicLevel NumberField.AdelicBox
open IsDedekindDomain AutomorphicForm

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.isSmoothCuspAutomorphicFnAt_rightConv_principalLevel_of_isFundamentalDomain_slab
    (L : Type) [Field L] [NumberField L]
    (α β : ℝ) (ΦL : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : ΦL ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range ΦL
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (ξL : (⊤ : Subgroup (AdeleRing (𝓞 L) L)ˣ) →* ℂˣ)
    (N : Ideal (𝓞 L)) (hN : N ≠ ⊥)
    (φ : AdelicGL2 (𝓞 L) L → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hφN : ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L, ∀ g : AdelicGL2 (𝓞 L) L, φ (u * g) = φ g)
    (v : AdelicGL2 (𝓞 L) L → ℂ) (hvc : Continuous v)
    (hv : IsCuspAutomorphicFnAt L
      (productionPinsOf L ΦL (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
        (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL v) :
    IsSmoothCuspAutomorphicFnAt L
        (productionPinsOf L ΦL (fun M => principalLevel (𝓞 L) L M ⊓ finiteAdelicGL2Subgroup L)
          (fun w => heckeGen (𝓞 L) L w) (adelicBox L)) ξL (rightConv L v φ) ∧
      Continuous (rightConv L v φ) ∧
      ∀ g : AdelicGL2 (𝓞 L) L, ∀ u ∈ principalLevel (𝓞 L) L N ⊓ finiteAdelicGL2Subgroup L,
        rightConv L v φ (g * u) = rightConv L v φ g := by sorry
