-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_algHom_cls_eq_cls_unitPullback
-- name    : AlgebraicGeometry.OModulePresheaf.exists_algHom_cls_eq_cls_unitPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/4ed6be71-caa3-5611-b872-b7d24ef7f66b
-- title:
--   Pull-back as graded R-algebra map of Čech rings
-- statement:
--   Fix a commutative ring $R$, schemes $X,Y$ with structure morphisms $\pi_X\colon X\to\operatorname{Spec} R$, $\pi_Y\colon Y\to\operatorname{Spec} R$, and a morphism $h\colon X\to Y$ with $h$ followed by $\pi_Y$ equal to $\pi_X$. Let $\mathcal W$, $\mathcal K$ be ordered affine covers of $X$, $Y$ (a finite linearly ordered index type, affine opens whose supremum is $\top$), and let $\mathrm{lam}\colon\mathcal W.\iota\to\mathcal K.\iota$ satisfy $\mathcal W.U_w\le h^{-1}(\mathcal K.U_{\mathrm{lam}\,w})$ for all $w$. For the presheaf of $\mathcal O$-modules `OModulePresheaf.unit` $\pi_Y$, namely $U\mapsto\Gamma(Y,U)$ with its $R$-algebra and restriction structure, the degree-$n$ cochains are families of sections over $\mathcal K.\mathrm{inter}\,s=\bigcap_j\mathcal K.U_{s_j}$ indexed by strictly increasing tuples $s$, with differential `d`; likewise for $\pi_X$ and $\mathcal W$. The hypotheses provide two "Čech-ring handles": a ring $H$ with an $R$-algebra structure, submodules $\mathcal A_n\subseteq H$ forming a graded monoid, and $R$-linear maps $\mathrm{cls}_n$ on the $n$-cocycles of $(\mathcal{K},\pi_Y)$ with range $\mathcal A_n$, such that $\mathrm{cls}_0$ is injective, $\mathrm{cls}_{n+1}z=0$ exactly when $z$ lies in the image of the degree-$n$ differential, $\mathrm{cls}$ is multiplicative for the cup product `cup` (whose value on two cocycles is asserted to be a cocycle), $H$ is the internal direct sum of the $\mathcal A_n$, and the cochain constantly $1$ is a $0$-cocycle with $\mathrm{cls}_0$-class $1$; and the same data $(H',\mathcal A',\mathrm{cls}')$ for $(\mathcal W,\pi_X)$, with no internality assumption imposed on $\mathcal A'$. The conclusion asserts the existence of an $R$-algebra homomorphism $p\colon H\to H'$ such that for every $n$ and every $n$-cocycle $z$ on $\mathcal K$ the alternating pull-back `OModulePresheaf.unitPullback` $h\,\mathcal W\,\mathcal K\,\mathrm{lam}$ of $z$ (sort $\mathrm{lam}\circ s$ when injective, with the sign of the sorting permutation, restrict along $h$; zero otherwise) is again a cocycle and $p(\mathrm{cls}_n z)$ equals its $\mathrm{cls}'_n$-class, and such that $p$ maps $\mathcal A_n$ into $\mathcal A'_n$ for every $n$.
--
--   This is the functoriality of the Čech cohomology ring of the structure sheaf under a morphism of $R$-schemes, stated for abstractly axiomatised class maps rather than for a particular construction of the ring, and pinned to the explicit alternating cochain-level pull-back. It is used in the good-reduction Jacobian development to produce graded algebra endomorphisms and Künneth-type comparisons of Čech rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_algHom_cls_eq_cls_unitPullback.lean

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

theorem AlgebraicGeometry.OModulePresheaf.exists_algHom_cls_eq_cls_unitPullback
    {R : Type u} [CommRing R] {X Y : Scheme.{u}} (πX : X ⟶ Spec (CommRingCat.of R)) (πY : Y ⟶ Spec (CommRingCat.of R))
    (h : X ⟶ Y) (hh : h ≫ πY = πX)
    (𝒲 : X.OrderedAffineCover) (𝒦 : Y.OrderedAffineCover) (lam : 𝒲.ι → 𝒦.ι) (hlam : ∀ w, 𝒲.U w ≤ h ⁻¹ᵁ 𝒦.U (lam w))
    (H : Type u) [Ring H] [Algebra R H] (𝒜 : ℕ → Submodule R H) [SetLike.GradedMonoid 𝒜]
    (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n)) →ₗ[R] H)
    (cls_range : ∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n)
    (cls_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 0)), cls 0 z = 0 ↔ z = 0)
    (cls_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 (n + 1)))),
      cls (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit πY).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit πY).d 𝒦 n))
    (cls_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 b))),
      ∃ hγ : (OModulePresheaf.unit πY).cup 𝒦 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 (a + b)),
        cls (a + b) ⟨_, hγ⟩ = cls a α * cls b β)
    (cls_internal : DirectSum.IsInternal 𝒜)
    (cls_one : ∃ h1 : (fun s => (1 : Γ(Y, 𝒦.inter s))) ∈ LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 0),
      cls 0 ⟨fun s => (1 : Γ(Y, 𝒦.inter s)), h1⟩ = 1)
    (H' : Type u) [Ring H'] [Algebra R H'] (𝒜' : ℕ → Submodule R H') [SetLike.GradedMonoid 𝒜']
    (cls' : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n)) →ₗ[R] H')
    (cls'_range : ∀ n : ℕ, LinearMap.range (cls' n) = 𝒜' n)
    (cls'_zero : ∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 0)), cls' 0 z = 0 ↔ z = 0)
    (cls'_succ : ∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 (n + 1)))),
      cls' (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit πX).cochain 𝒲 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit πX).d 𝒲 n))
    (cls'_mul : ∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 b))),
      ∃ hγ : (OModulePresheaf.unit πX).cup 𝒲 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 (a + b)),
        cls' (a + b) ⟨_, hγ⟩ = cls' a α * cls' b β)
    (cls'_one : ∃ h1 : (fun s => (1 : Γ(X, 𝒲.inter s))) ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 0),
      cls' 0 ⟨fun s => (1 : Γ(X, 𝒲.inter s)), h1⟩ = 1)
    :
    ∃ p : H →ₐ[R] H',
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit πY).d 𝒦 n))),
        ∃ hz : OModulePresheaf.unitPullback (πX := πX) h 𝒲 𝒦 lam hlam n z.1 ∈ LinearMap.ker ((OModulePresheaf.unit πX).d 𝒲 n),
          p (cls n z) = cls' n ⟨_, hz⟩) ∧
      (∀ n : ℕ, (𝒜 n).map p.toLinearMap ≤ 𝒜' n) := by sorry
