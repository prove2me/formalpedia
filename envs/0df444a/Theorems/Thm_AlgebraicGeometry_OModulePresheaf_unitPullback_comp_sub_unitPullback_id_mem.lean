-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_comp_sub_unitPullback_id_mem
-- name    : AlgebraicGeometry.OModulePresheaf.unitPullback_comp_sub_unitPullback_id_mem
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/62754010-587a-5062-aa28-ee7e3c9d2a60
-- title:
--   Composing pinning relations for pull-backs of Čech cocycles
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, and $\pi_X \colon X \to \operatorname{Spec} R$ a separated morphism with $X$ quasi-compact; let $\varphi, \psi \colon X \to X$ be endomorphisms and let $\mathcal{K}$ be an ordered affine cover of $X$, i.e. a finite linearly ordered index type together with affine opens covering $X$. Cochains are taken for the $\mathcal{O}$-module presheaf `OModulePresheaf.unit` $\pi_X$, whose value on an open $U$ is $\Gamma(X,U)$ with its $R$-algebra structure coming from $\pi_X$, so that an $n$-cochain on a cover assigns to each strictly increasing $(n+1)$-tuple of indices a section over the intersection of the corresponding opens; `d` is the Čech differential and `unitPullback` $h$ the pull-back along a morphism $h$ relative to an index map refining the cover, defined tuple-wise by the signed (by the sign of the sorting permutation) restriction of $h^{\sharp}$ applied to the value of the cochain at the sorted index tuple, and by $0$ when the index map is not injective on the tuple. Fix $n \in \mathbb{N}$ and $n$-cochains $z, z', z''$ on $\mathcal{K}$ with $dz = dz' = dz'' = 0$. Assume given: an ordered affine cover $\mathcal{V}_1$ with index maps $\lambda_1, \lambda_1'$ to the indices of $\mathcal{K}$ satisfying $\mathcal{V}_1.U(v) \le \psi^{-1}(\mathcal{K}.U(\lambda_1 v))$ and $\mathcal{V}_1.U(v) \le \mathrm{id}^{-1}(\mathcal{K}.U(\lambda_1' v))$, such that $\psi^{*}_{\lambda_1} z - \mathrm{id}^{*}_{\lambda_1'} z'$ lies in the $R$-submodule of $n$-cochains on $\mathcal{V}_1$ which is $\bot$ when $n = 0$ and the range of $d_{\mathcal{V}_1}$ on $(n-1)$-cochains when $n \ge 1$; and likewise a cover $\mathcal{V}_2$ with $\lambda_2, \lambda_2'$ refining $\mathcal{K}$ along $\varphi$ and along $\mathrm{id}$, with $\varphi^{*}_{\lambda_2} z' - \mathrm{id}^{*}_{\lambda_2'} z''$ in the corresponding submodule for $\mathcal{V}_2$. Then for every ordered affine cover $\mathcal{V}_3$ and index maps $\lambda_3, \lambda_3'$ with $\mathcal{V}_3.U(v) \le (\psi \circ \varphi)^{-1}(\mathcal{K}.U(\lambda_3 v))$ and $\mathcal{V}_3.U(v) \le \mathrm{id}^{-1}(\mathcal{K}.U(\lambda_3' v))$, the difference $(\varphi \text{ followed by } \psi)^{*}_{\lambda_3} z - \mathrm{id}^{*}_{\lambda_3'} z''$ lies in the analogous submodule for $\mathcal{V}_3$, namely $\bot$ for $n = 0$ and the image of $d_{\mathcal{V}_3}$ for $n \ge 1$.
--
--   This is the composition law for the relation "the pull-back along a morphism carries the class of $z$ to the class of $z'$", expressed concretely on ordered affine covers and independently of the choice of refining cover and index maps: it encodes the contravariant functoriality $(\varphi \text{ followed by } \psi)^{*} = \varphi^{*} \circ \psi^{*}$ on Čech cohomology classes of the structure sheaf. It is used in the construction of the algebra homomorphism attached to endomorphisms of a Jacobian with good reduction, in [`GoodReductionJacobian.AbelianSchemePropertyBundle.exists_endo_algHom_pinned_unitPullback_of_cls_cup`](thm.html#GoodReductionJacobian.AbelianSchemePropertyBundle.exists_endo_algHom_pinned_unitPullback_of_cls_cup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_comp_sub_unitPullback_id_mem.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_comp_sub_unitPullback_id_mem
    {R : Type u} [CommRing R] {X : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R)) [IsSeparated πX] [CompactSpace X]
    (φ ψ : X ⟶ X) (𝒦 : X.OrderedAffineCover)

    (𝒱₁ : X.OrderedAffineCover) (lam₁ lam₁' : 𝒱₁.ι → 𝒦.ι)
    (hl₁ : ∀ v, 𝒱₁.U v ≤ ψ ⁻¹ᵁ 𝒦.U (lam₁ v)) (hl₁' : ∀ v, 𝒱₁.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam₁' v))

    (𝒱₂ : X.OrderedAffineCover) (lam₂ lam₂' : 𝒱₂.ι → 𝒦.ι)
    (hl₂ : ∀ v, 𝒱₂.U v ≤ φ ⁻¹ᵁ 𝒦.U (lam₂ v)) (hl₂' : ∀ v, 𝒱₂.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam₂' v))
    (n : ℕ) (z z' z'' : (OModulePresheaf.unit πX).cochain 𝒦 n)
    (hz : (OModulePresheaf.unit πX).d 𝒦 n z = 0) (hz' : (OModulePresheaf.unit πX).d 𝒦 n z' = 0)
    (hz'' : (OModulePresheaf.unit πX).d 𝒦 n z'' = 0)
    (h₁ : OModulePresheaf.unitPullback (πX := πX) ψ 𝒱₁ 𝒦 lam₁ hl₁ n z -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₁ 𝒦 lam₁' hl₁' n z'
      ∈ (show Submodule R ((OModulePresheaf.unit πX).cochain 𝒱₁ n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₁ m)))
    (h₂ : OModulePresheaf.unitPullback (πX := πX) φ 𝒱₂ 𝒦 lam₂ hl₂ n z' -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₂ 𝒦 lam₂' hl₂' n z''
      ∈ (show Submodule R ((OModulePresheaf.unit πX).cochain 𝒱₂ n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₂ m)))

    (𝒱₃ : X.OrderedAffineCover) (lam₃ lam₃' : 𝒱₃.ι → 𝒦.ι)
    (hl₃ : ∀ v, 𝒱₃.U v ≤ (φ ≫ ψ) ⁻¹ᵁ 𝒦.U (lam₃ v)) (hl₃' : ∀ v, 𝒱₃.U v ≤ (𝟙 X) ⁻¹ᵁ 𝒦.U (lam₃' v)) :
    OModulePresheaf.unitPullback (πX := πX) (φ ≫ ψ) 𝒱₃ 𝒦 lam₃ hl₃ n z -
        OModulePresheaf.unitPullback (πX := πX) (𝟙 X) 𝒱₃ 𝒦 lam₃' hl₃' n z''
      ∈ (show Submodule R ((OModulePresheaf.unit πX).cochain 𝒱₃ n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₃ m)) := by sorry
