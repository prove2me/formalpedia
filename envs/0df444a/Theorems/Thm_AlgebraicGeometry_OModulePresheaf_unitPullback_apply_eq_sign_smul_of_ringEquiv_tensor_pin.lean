-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin
-- name    : AlgebraicGeometry.OModulePresheaf.unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/8f0506dc-0b3d-5a7b-82a1-161740d3d126
-- title:
--   Pulled-back unit cochain as signed transport through θ
-- statement:
--   Let $R$ be a commutative ring, $Y$ a scheme and $\pi : Y \to \operatorname{Spec} R$ a separated morphism, let $A$ be an $R$-algebra, and let $\mathcal U, \mathcal V$ be ordered affine covers of $Y$ (each given by a finite linearly ordered index type and affine opens whose supremum is $\top$); write $Y_A = Y \times_{\operatorname{Spec} R} \operatorname{Spec} A$ with projections $\mathrm{pr}_1, \mathrm{pr}_2$, and let $\mathcal U_A, \mathcal V_A$ be the covers of $Y_A$ obtained by taking $\mathrm{pr}_1$-preimages. Assume given an endomorphism $h$ of $Y_A$ with $h$ followed by $\mathrm{pr}_2$ equal to $\mathrm{pr}_2$, a map $\lambda : \mathcal V.\iota \to \mathcal U.\iota$ with $\mathcal V_{A,v} \le h^{-1}\mathcal U_{A,\lambda v}$ for all $v$, a degree $n$, a cochain $z$ assigning to each strictly monotone $(n+1)$-tuple $t$ in $\mathcal U.\iota$ an element of $\Gamma(Y_A, \bigcap_j \mathcal U_{A, t_j})$, and a strictly monotone $(n+1)$-tuple $s$ in $\mathcal V.\iota$ with $\lambda \circ s$ injective; let $t$ denote the strictly increasing reordering of $\lambda \circ s$ by $\mathrm{Tuple.sort}$. Assume further: ring isomorphisms $\sigma : A \otimes_R \Gamma(Y, \mathcal U_t) \cong \Gamma(Y_A, \mathcal U_{A,t})$ and $\sigma_V : A \otimes_R \Gamma(Y, \mathcal V_s) \cong \Gamma(Y_A, \mathcal V_{A,s})$, each pinned by sending $1 \otimes y$ to the restriction of $\mathrm{pr}_1^\sharp(y)$ and $a \otimes 1$ to the image of $a$ under the structure map coming from $\mathrm{pr}_2$ (the $R$-algebra structures on sections being those induced by $\pi$); an $R$-algebra map $\theta : \Gamma(Y, \mathcal U_t) \to \Gamma(Y, \mathcal V_s)$ such that for every $y$ the restriction to $\mathcal V_{A,s}$ of $h^\sharp$ applied to the restriction of $\mathrm{pr}_1^\sharp(y)$ to $\mathcal U_{A,t}$ equals the restriction of $\mathrm{pr}_1^\sharp(\theta y)$; and an element $x \in A \otimes_R \Gamma(Y, \mathcal U_t)$ with $\sigma(x) = z(t)$. Then the value at $s$ of the pulled-back cochain `OModulePresheaf.unitPullback` for $h$, from $\mathcal U_A$ to $\mathcal V_A$ along $\lambda$, equals $\operatorname{sign}(\mathrm{Tuple.sort}(\lambda \circ s)) \cdot \sigma_V\bigl((\mathrm{id}_A \otimes \theta)(x)\bigr)$, the sign being taken as an integer acting by scalar multiplication.
--
--   This identifies, in the tensor-product model $A \otimes_R \Gamma(Y, -)$ of sections over a base change, the refinement (pullback along $h$ and $\lambda$) of a Čech cochain with coefficients in the structure sheaf: on a simplex whose image under $\lambda$ is injective, the value is the signed image of the value at the sorted simplex under $\mathrm{id}_A \otimes \theta$. It is used in the construction of obstruction cocycles for bare deformations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin.lean

import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverComap
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Scheme.TwoAffineOpenCover
open scoped TensorProduct

universe u

theorem AlgebraicGeometry.OModulePresheaf.unitPullback_apply_eq_sign_smul_of_ringEquiv_tensor_pin
    {R : Type u} [CommRing R] {Y : Scheme.{u}} (π : Y ⟶ Spec (CommRingCat.of R)) [IsSeparated π]
    (A : Type u) [CommRing A] [Algebra R A]
    (𝒰 𝒱 : Y.OrderedAffineCover)

    (h : pullback π (specMap R A) ⟶ pullback π (specMap R A))
    (hh : h ≫ pullback.snd π (specMap R A) = pullback.snd π (specMap R A))
    (lam : 𝒱.ι → 𝒰.ι) (hl : ∀ v, (𝒱.baseChange π A).U v ≤ h ⁻¹ᵁ (𝒰.baseChange π A).U (lam v))
    (n : ℕ) (z : (OModulePresheaf.unit (pullback.snd π (specMap R A))).cochain (𝒰.baseChange π A) n)
    (s : 𝒱.Idx n) (hinj : Function.Injective (lam ∘ s.1))

    (σ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      (A ⊗[R] Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))) ≃+*
        Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))
    (hσ₁ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      ∀ y : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)),
        σ ((1 : A) ⊗ₜ[R] y) =
          ((pullback π (specMap R A)).presheaf.map
              (homOfLE (𝒰.baseChange_inter_le π A ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).op).hom
            (((pullback.fst π (specMap R A)).app (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom y))
    (hσ₂ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom (pullback.snd π (specMap R A))
        ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      ∀ a : A, σ (a ⊗ₜ[R] (1 : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))) =
        algebraMap A Γ(pullback π (specMap R A), (𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) a)
    (σV : letI := algebraOfHom π (𝒱.inter s)
      (A ⊗[R] Γ(Y, 𝒱.inter s)) ≃+* Γ(pullback π (specMap R A), (𝒱.baseChange π A).inter s))
    (hσV₁ : letI := algebraOfHom π (𝒱.inter s)
      ∀ y : Γ(Y, 𝒱.inter s),
        σV ((1 : A) ⊗ₜ[R] y) =
          ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒱.baseChange_inter_le π A s)).op).hom
            (((pullback.fst π (specMap R A)).app (𝒱.inter s)).hom y))
    (hσV₂ : letI := algebraOfHom π (𝒱.inter s)
      letI := algebraOfHom (pullback.snd π (specMap R A)) ((𝒱.baseChange π A).inter s)
      ∀ a : A, σV (a ⊗ₜ[R] (1 : Γ(Y, 𝒱.inter s))) = algebraMap A Γ(pullback π (specMap R A), (𝒱.baseChange π A).inter s) a)

    (θ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom π (𝒱.inter s)
      Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) →ₐ[R] Γ(Y, 𝒱.inter s))
    (hθ : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      letI := algebraOfHom π (𝒱.inter s)
      ∀ y : Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)),
        ((pullback π (specMap R A)).presheaf.map
            (homOfLE ((𝒱.baseChange π A).inter_le_preimage_inter_sortIdx h (𝒰.baseChange π A) lam hl s hinj)).op).hom
          ((h.app ((𝒰.baseChange π A).inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom
            (((pullback π (specMap R A)).presheaf.map
                (homOfLE (𝒰.baseChange_inter_le π A ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).op).hom
              (((pullback.fst π (specMap R A)).app (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))).hom y))) =
        ((pullback π (specMap R A)).presheaf.map (homOfLE (𝒱.baseChange_inter_le π A s)).op).hom
          (((pullback.fst π (specMap R A)).app (𝒱.inter s)).hom (θ y)))

    (x : letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
      A ⊗[R] Γ(Y, 𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)))
    (hx : σ x = z ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj)) :
    letI := algebraOfHom π (𝒰.inter ((𝒱.baseChange π A).sortIdx (𝒰.baseChange π A) lam s hinj))
    letI := algebraOfHom π (𝒱.inter s)
    OModulePresheaf.unitPullback (πX := pullback.snd π (specMap R A)) h (𝒱.baseChange π A) (𝒰.baseChange π A) lam hl n z s =
      ((Equiv.Perm.sign (Tuple.sort (lam ∘ s.1)) : ℤˣ) : ℤ) •
        σV ((Algebra.TensorProduct.map (AlgHom.id A A) θ) x) := by sorry
