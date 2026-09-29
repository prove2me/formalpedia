-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_kunneth_injective_of_cls_unitPullback
-- name    : AlgebraicGeometry.OModulePresheaf.kunneth_injective_of_cls_unitPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/895dc1ce-81b9-5905-b644-e7966331fc5f
-- title:
--   Künneth injectivity for Čech cocycle class maps
-- statement:
--   Let $k$ be a field and $f\colon A\to\operatorname{Spec} k$ a separated morphism of schemes. Let $\mathcal K$ be an ordered affine cover of $A$ (a finite linearly ordered index set together with affine opens whose supremum is $\top$) and $\mathcal W$ one of $A\times_k A$, and let $\mathrm{lam}_1,\mathrm{lam}_2\colon \mathcal W.\iota\to\mathcal K.\iota$ satisfy $\mathcal W.U(w)\le \mathrm{pr}_1^{-1}\mathcal K.U(\mathrm{lam}_1 w)$ and $\mathcal W.U(w)\le \mathrm{pr}_2^{-1}\mathcal K.U(\mathrm{lam}_2 w)$. Let $H$ be a $k$-algebra with submodules $\mathcal A_n\subseteq H$ forming a graded monoid, equipped with $k$-linear maps $\mathrm{cls}_n$ on the cocycles $\ker\big((\mathrm{unit}\,f).d\,\mathcal K\,n\big)$ of the Čech cochain complex of the structure presheaf $U\mapsto\Gamma(A,U)$, such that $\operatorname{range}\mathrm{cls}_n=\mathcal A_n$, $\mathrm{cls}_0$ is injective, and for $n\ge 0$ a cocycle $z$ in degree $n+1$ has $\mathrm{cls}_{n+1}z=0$ exactly when $z$ is a coboundary. Let $(H',\mathcal A',\mathrm{cls}')$ be such data for $\mathcal W$ and the structure morphism $\mathrm{pr}_1$ followed by $f$, with $\mathrm{cls}'$ additionally multiplicative for the Čech cup product (the cup product of cocycles being a cocycle, with class the product of the classes) and $\mathcal A'$ an internal direct sum decomposition of $H'$. Finally let $p_1,p_2\colon H\to H'$ be $k$-algebra maps with $p_i(\mathrm{cls}_n z)=\mathrm{cls}'_n$ of the cochain pullback `unitPullback` of $z$ along $\mathrm{pr}_i$ through $\mathrm{lam}_i$ (which is asserted to be a cocycle). Then the $k$-linear map $\bigoplus_{(a,b)\in\mathbb N^2}\mathcal A_a\otimes_k\mathcal A_b\to H'$ determined by $u\otimes v\mapsto p_1(u)\,p_2(v)$ is injective.
--
--   This is the injectivity half of the Künneth formula for the Čech cohomology ring of $A\times_k A$ over a field, formulated entirely in terms of abstract class maps $\mathrm{cls}$, $\mathrm{cls}'$ presenting the cohomology of the two ordered affine covers as graded algebras. It is used in the study of the Jacobian with good reduction, where it supplies the Künneth hypothesis of the statements producing graded-monoid structures and cup-product decompositions of low-degree Čech classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_kunneth_injective_of_cls_unitPullback.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u

theorem AlgebraicGeometry.OModulePresheaf.kunneth_injective_of_cls_unitPullback
    {k : Type u} [Field k] {A : Scheme.{u}} (f : A ⟶ Spec (CommRingCat.of k)) [IsSeparated f]
    (𝒦 : A.OrderedAffineCover)
    (𝒲 : (pullback f f).OrderedAffineCover) (lam₁ lam₂ : 𝒲.ι → 𝒦.ι)
    (h₁ : ∀ w, 𝒲.U w ≤ pullback.fst f f ⁻¹ᵁ 𝒦.U (lam₁ w))
    (h₂ : ∀ w, 𝒲.U w ≤ pullback.snd f f ⁻¹ᵁ 𝒦.U (lam₂ w))
    (H : Type u) [Ring H] [Algebra k H] (𝒜 : ℕ → Submodule k H) [SetLike.GradedMonoid 𝒜]
    (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n)) →ₗ[k] H)
    (cls_range : ∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n)
    (cls_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 0)), cls 0 z = 0 ↔ z = 0)
    (cls_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 (n + 1)))),
      cls (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit f).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit f).d 𝒦 n))
    (H' : Type u) [Ring H'] [Algebra k H'] (𝒜' : ℕ → Submodule k H') [SetLike.GradedMonoid 𝒜']
    (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n)) →ₗ[k] H')
    (cls'_range : ∀ n : ℕ, LinearMap.range (cls' n) = 𝒜' n)
    (cls'_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 0)), cls' 0 z = 0 ↔ z = 0)
    (cls'_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (n + 1)))),
      cls' (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cochain 𝒲 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n))
    (cls'_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 b))),
      ∃ hγ : (OModulePresheaf.unit (pullback.fst f f ≫ f)).cup 𝒲 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 (a + b)),
        cls' (a + b) ⟨_, hγ⟩ = cls' a α * cls' b β)
    (cls'_internal : DirectSum.IsInternal 𝒜')
    (p₁ p₂ : H →ₐ[k] H')
    (hp₁ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
      ∃ hz : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.fst f f) 𝒲 𝒦 lam₁ h₁ n z.1 ∈
          LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n),
        p₁ (cls n z) = cls' n ⟨_, hz⟩)
    (hp₂ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit f).d 𝒦 n))),
      ∃ hz : OModulePresheaf.unitPullback (πX := pullback.fst f f ≫ f) (pullback.snd f f) 𝒲 𝒦 lam₂ h₂ n z.1 ∈
          LinearMap.ker ((OModulePresheaf.unit (pullback.fst f f ≫ f)).d 𝒲 n),
        p₂ (cls n z) = cls' n ⟨_, hz⟩) :
    Function.Injective (DirectSum.toModule k (ℕ × ℕ) H' fun ab : ℕ × ℕ =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 ab.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 ab.2).subtype)) := by sorry
