-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_mem_refinement
-- name    : AlgebraicGeometry.OModulePresheaf.unitPullback_sub_unitPullback_mem_of_mem_refinement
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/9c174752-a5e0-5d1c-9650-34c6b07dd85a
-- title:
--   Refinement independence of differences of Čech pullbacks
-- statement:
--   Let $R,R'$ be commutative rings, let $X,Y$ be schemes, let $\pi_X\colon X\to\operatorname{Spec} R'$ be separated with $X$ quasi-compact, let $\pi_Y\colon Y\to\operatorname{Spec} R$ be arbitrary, and let $g,g'\colon X\to Y$ be two morphisms. Let $\mathcal K$ be an ordered affine cover of $Y$ (a finite linearly ordered family of affine opens with supremum $\top$) and let $\mathcal V_1,\mathcal V_2$ be ordered affine covers of $X$, equipped with index maps $\lambda_1,\lambda_1'\colon \mathcal V_1.\iota\to\mathcal K.\iota$ and $\lambda_2,\lambda_2'\colon \mathcal V_2.\iota\to\mathcal K.\iota$ such that $\mathcal V_k.U(v)\le g^{-1}\mathcal K.U(\lambda_k v)$ and $\mathcal V_k.U(v)\le g'^{-1}\mathcal K.U(\lambda_k' v)$ for all $v$ and $k=1,2$. Let $n\in\mathbb N$ and let $z,z'$ be degree-$n$ cochains for the presheaf `OModulePresheaf.unit` $\pi_Y$ on $\mathcal K$, that is, families of sections of $\mathcal O_Y$ over the intersections $\bigcap_j \mathcal K.U(s_j)$ indexed by the strictly increasing tuples $s$, both annihilated by the Čech differential $d$. Here `unitPullback` sends such a cochain to the cochain on $\mathcal V_k$ whose value at $s$ is zero unless $\lambda\circ s$ is injective, and otherwise is the sign of the sorting permutation times the restriction to $\bigcap_j\mathcal V_k.U(s_j)$ of the pullback along the relevant morphism of the value of $z$ at the sorted tuple. The assertion is: if the difference of the pullback of $z$ along $g$ via $\lambda_1$ and the pullback of $z'$ along $g'$ via $\lambda_1'$ lies in the submodule of $R'$-cochains on $\mathcal V_1$ which is $\bot$ for $n=0$ and the image of $d$ in degree $m$ for $n=m+1$, then the corresponding difference of pullbacks computed on $\mathcal V_2$ via $\lambda_2,\lambda_2'$ lies in the analogous submodule of cochains on $\mathcal V_2$.
--
--   This is the well-definedness statement needed to compare Čech classes pulled back along two morphisms: the relation '$g^*[z]=g'^*[z']$', read at the level of cochains on a cover of $X$ refining $\mathcal K$, does not depend on the refinement chosen. It is used in the comparison of `unitPullback` along a composite with the identity pullback, in the statement that equal composites give cohomologous pulled-back cocycles, and in the construction of pinned endomorphism algebra maps for the Jacobian with good reduction.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_sub_unitPullback_mem_of_mem_refinement.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_sub_unitPullback_mem_of_mem_refinement
    {R R' : Type u} [CommRing R] [CommRing R'] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (CommRingCat.of R')) [IsSeparated πX] [CompactSpace X] (πY : Y ⟶ Spec (CommRingCat.of R))
    (g g' : X ⟶ Y) (𝒦 : Y.OrderedAffineCover)
    (𝒱₁ : X.OrderedAffineCover) (lam₁ lam₁' : 𝒱₁.ι → 𝒦.ι)
    (hl₁ : ∀ v, 𝒱₁.U v ≤ g ⁻¹ᵁ 𝒦.U (lam₁ v)) (hl₁' : ∀ v, 𝒱₁.U v ≤ g' ⁻¹ᵁ 𝒦.U (lam₁' v))
    (𝒱₂ : X.OrderedAffineCover) (lam₂ lam₂' : 𝒱₂.ι → 𝒦.ι)
    (hl₂ : ∀ v, 𝒱₂.U v ≤ g ⁻¹ᵁ 𝒦.U (lam₂ v)) (hl₂' : ∀ v, 𝒱₂.U v ≤ g' ⁻¹ᵁ 𝒦.U (lam₂' v))
    (n : ℕ) (z z' : (OModulePresheaf.unit πY).cochain 𝒦 n)
    (hz : (OModulePresheaf.unit πY).d 𝒦 n z = 0) (hz' : (OModulePresheaf.unit πY).d 𝒦 n z' = 0)
    (h₁ : OModulePresheaf.unitPullback (πX := πX) g 𝒱₁ 𝒦 lam₁ hl₁ n z -
        OModulePresheaf.unitPullback (πX := πX) g' 𝒱₁ 𝒦 lam₁' hl₁' n z'
      ∈ (show Submodule R' ((OModulePresheaf.unit πX).cochain 𝒱₁ n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₁ m))) :
    OModulePresheaf.unitPullback (πX := πX) g 𝒱₂ 𝒦 lam₂ hl₂ n z -
        OModulePresheaf.unitPullback (πX := πX) g' 𝒱₂ 𝒦 lam₂' hl₂' n z'
      ∈ (show Submodule R' ((OModulePresheaf.unit πX).cochain 𝒱₂ n) from
          match n with
          | 0 => ⊥
          | m + 1 => LinearMap.range ((OModulePresheaf.unit πX).d 𝒱₂ m)) := by sorry
