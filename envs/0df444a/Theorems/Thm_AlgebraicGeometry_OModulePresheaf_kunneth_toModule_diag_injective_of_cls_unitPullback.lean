-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_kunneth_toModule_diag_injective_of_cls_unitPullback
-- name    : AlgebraicGeometry.OModulePresheaf.kunneth_toModule_diag_injective_of_cls_unitPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/5eb44d31-b9c4-53e6-bf52-5d7efa12e448
-- title:
--   Per-degree Künneth injectivity for Čech classes
-- statement:
--   Let $k$ be a field, $A$ a scheme and $f : A \to \operatorname{Spec} k$ a separated morphism. Let $\mathcal K$ be an ordered affine cover of $A$ (a finite linearly ordered index set together with affine opens whose supremum is $\top$) and $\mathcal W$ an ordered affine cover of $A \times_k A$, and let $\mathrm{lam}_1, \mathrm{lam}_2 : \mathcal W.\iota \to \mathcal K.\iota$ satisfy $\mathcal W.U\,w \le \mathrm{pr}_1^{-1}(\mathcal K.U\,(\mathrm{lam}_1 w))$ and $\mathcal W.U\,w \le \mathrm{pr}_2^{-1}(\mathcal K.U\,(\mathrm{lam}_2 w))$ for all $w$, where $\mathrm{pr}_1,\mathrm{pr}_2$ are the two projections `pullback.fst f f`, `pullback.snd f f`. Throughout, `OModulePresheaf.unit` denotes the presheaf $U \mapsto \Gamma(\cdot, U)$ with its $k$-module structure coming from the structure morphism, its Čech cochain module in degree $n$ being the sections of this presheaf over the intersections $\bigcap_j U_{s(j)}$ indexed by the strictly increasing index tuples $s$, and `d` its Čech differential. Let $H$ be a $k$-algebra with a family of $k$-submodules $\mathcal A : \mathbb N \to \mathrm{Submodule}\,k\,H$ forming a graded monoid, and let $\mathrm{cls}_n$ be $k$-linear maps from the degree-$n$ cocycles of `unit f` on $\mathcal K$ to $H$ with image exactly $\mathcal A_n$, injective in degree $0$, and with $\mathrm{cls}_{n+1}(z) = 0$ exactly when $z$ is a coboundary. Let $H', \mathcal A', \mathrm{cls}'$ be the analogous data for the presheaf `unit (pullback.fst f f ≫ f)` on the cover $\mathcal W$ of $A \times_k A$, subject in addition to: $\mathrm{cls}'$ turns the Alexander–Whitney cup product `cup` of cocycles in degrees $a$ and $b$ (again a cocycle) into the product $\mathrm{cls}'_a(\alpha)\,\mathrm{cls}'_b(\beta)$ in $H'$, and $\mathcal A'$ makes $H'$ an internal direct sum. Let $p_1, p_2 : H \to H'$ be $k$-algebra maps pinned to pullback of cochains: for every $n$ and every degree-$n$ cocycle $z$ on $\mathcal K$, the cochain `unitPullback` of $z$ along $\mathrm{pr}_1$ with $\mathrm{lam}_1$ (respectively along $\mathrm{pr}_2$ with $\mathrm{lam}_2$) is a cocycle on $\mathcal W$ and $p_1(\mathrm{cls}_n z)$ (respectively $p_2(\mathrm{cls}_n z)$) is its class under $\mathrm{cls}'_n$. Then, for every $n \in \mathbb N$, the $k$-linear map $$\bigoplus_{a+b=n} \mathcal A_a \otimes_k \mathcal A_b \longrightarrow H', \qquad u \otimes v \mapsto p_1(u)\,p_2(v),$$ indexed by [`DoubleComplex.Diag n`](def/AlgebraicGeometry_DoubleComplex.html#L34) $= \{(a,b) : a+b = n\}$, is injective.
--
--   This is the Künneth statement for the Čech cohomology of the structure sheaf of $A$ over $k$, in the form needed for the product $A \times_k A$: in each fixed total degree the cup product of pullbacks along the two projections is injective on the diagonal sum of tensor products of graded pieces. It is the geometric ingredient of [`AlgebraicGeometry.OModulePresheaf.kunneth_injective_of_cls_unitPullback`](thm.html#AlgebraicGeometry.OModulePresheaf.kunneth_injective_of_cls_unitPullback), which combines it with the internal grading of $H'$ to get injectivity of the full Künneth map.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_kunneth_toModule_diag_injective_of_cls_unitPullback.lean

import Mathlib
import Definitions.Def_JacJ1Iface
import Definitions.Def_AlgebraicGeometry_RelativeGroupLaw
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_DoubleComplex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open scoped TensorProduct DirectSum

universe u

theorem AlgebraicGeometry.OModulePresheaf.kunneth_toModule_diag_injective_of_cls_unitPullback
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
        p₂ (cls n z) = cls' n ⟨_, hz⟩)
    (n : ℕ) :
    Function.Injective (DirectSum.toModule k (DoubleComplex.Diag n) H' fun i : DoubleComplex.Diag n =>
      LinearMap.mul' k H' ∘ₗ
        TensorProduct.map (p₁.toLinearMap ∘ₗ (𝒜 i.1.1).subtype) (p₂.toLinearMap ∘ₗ (𝒜 i.1.2).subtype)) := by sorry
