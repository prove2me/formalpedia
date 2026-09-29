-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_gradedMonoid_cls_cup_unit
-- name    : AlgebraicGeometry.OModulePresheaf.exists_gradedMonoid_cls_cup_unit
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/d6186b15-02fa-5464-a1a8-d0600e58d59c
-- title:
--   Graded Čech ring of the structure sheaf on an ordered affine cover
-- statement:
--   Let $R$ be a commutative ring, $X$ a scheme, $\pi \colon X \to \operatorname{Spec} R$ a morphism, and $\mathcal{K}$ an ordered affine cover of $X$, that is, a finite linearly ordered index type together with affine opens $U_i$ whose supremum is $\top$. Write $\mathcal{O} =$ `unit π` for the structure sheaf regarded as a presheaf of modules over $R$ and over the sections rings, with $R$-algebra structures induced by $\pi$; its degree-$n$ cochains are the families $\alpha_s \in \Gamma(X, \mathcal{K}.\mathrm{inter}\,s)$ indexed by the increasing index tuples $s$ of degree $n$, where $\mathcal{K}.\mathrm{inter}\,s = \bigsqcap_j U_{s_j}$, and $d$ denotes the associated alternating Čech differential. The assertion is that there exist a ring $H$, an $R$-algebra structure on it, a family of $R$-submodules $\mathcal{A}_n \subseteq H$ forming a graded monoid ($1 \in \mathcal{A}_0$ and $\mathcal{A}_a\mathcal{A}_b \subseteq \mathcal{A}_{a+b}$), and $R$-linear maps $\mathrm{cls}_n \colon \ker d^n \to H$ such that: the range of $\mathrm{cls}_n$ is $\mathcal{A}_n$; the family $\mathcal{A}$ decomposes $H$ internally as a direct sum; $\mathrm{cls}_0 z = 0$ only for $z = 0$; for $n \ge 0$ and $z \in \ker d^{n+1}$, $\mathrm{cls}_{n+1} z = 0$ exactly when $z$ lies in the range of $d^n$; for cocycles $\alpha \in \ker d^a$ and $\beta \in \ker d^b$, the cup product `cup 𝒦 a b (a+b) rfl α β` (the product of the restrictions of $\alpha$ along the front face and $\beta$ along the back face) lies in $\ker d^{a+b}$ and has class $\mathrm{cls}_a\alpha \cdot \mathrm{cls}_b\beta$; and the cochain constantly equal to $1 \in \Gamma(X, \mathcal{K}.\mathrm{inter}\,s)$ lies in $\ker d^0$ with class $1 \in H$.
--
--   This packages the alternating Čech cohomology $\bigoplus_n \check H^n(\mathcal{K}, \mathcal{O}_X)$ of the structure sheaf on a finite ordered affine cover as a graded $R$-algebra, with the cup product of cocycles inducing the multiplication and the class maps identifying each graded piece; graded commutativity is not part of the package. It is used in the treatment of good reduction of Jacobians, notably in the constructions of Künneth-type injectivity and of algebra endomorphisms attached to classes on pullbacks of the structure sheaf.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_gradedMonoid_cls_cup_unit.lean

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

theorem AlgebraicGeometry.OModulePresheaf.exists_gradedMonoid_cls_cup_unit
    {R : Type u} [CommRing R] {X : Scheme.{u}} (π : X ⟶ Spec (CommRingCat.of R)) (𝒦 : X.OrderedAffineCover) :
    ∃ (H : Type u) (_ : Ring H) (_ : Algebra R H) (𝒜 : ℕ → Submodule R H) (_ : SetLike.GradedMonoid 𝒜)
      (cls : ∀ n : ℕ, ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 n)) →ₗ[R] H),
      (∀ n : ℕ, LinearMap.range (cls n) = 𝒜 n) ∧
      DirectSum.IsInternal 𝒜 ∧
      (∀ z : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 0)), cls 0 z = 0 ↔ z = 0) ∧
      (∀ (n : ℕ) (z : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 (n + 1)))),
        cls (n + 1) z = 0 ↔ (z : (OModulePresheaf.unit π).cochain 𝒦 (n + 1)) ∈ LinearMap.range ((OModulePresheaf.unit π).d 𝒦 n)) ∧
      (∀ (a b : ℕ) (α : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 a))) (β : ↥(LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 b))),
        ∃ hγ : (OModulePresheaf.unit π).cup 𝒦 a b (a + b) rfl α.1 β.1 ∈ LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 (a + b)),
          cls (a + b) ⟨_, hγ⟩ = cls a α * cls b β) ∧
      (∃ h1 : (fun s => (1 : Γ(X, 𝒦.inter s))) ∈ LinearMap.ker ((OModulePresheaf.unit π).d 𝒦 0),
        cls 0 ⟨fun s => (1 : Γ(X, 𝒦.inter s)), h1⟩ = 1) := by sorry
