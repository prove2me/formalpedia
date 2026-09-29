-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral
-- name    : AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/9b62fe10-657e-5297-9680-4224e07dca8d
-- title:
--   Dévissage for coherent data with support on a proper scheme
-- statement:
--   Let $R$ be a Noetherian commutative ring, $V$ a scheme and $\pi : V \to \operatorname{Spec} R$ a proper morphism. The objects considered are `OModulePresheaf π`: assignments $U \mapsto G(U)$ of an abelian group to each open $U \subseteq V$ carrying compatible $R$- and $\Gamma(V,U)$-module structures together with $R$-linear restriction maps $G(U') \to G(U)$ for $U \le U'$, semilinear over restriction of functions and satisfying the presheaf identities; such a $G$ is `IsCoherent` when $G(U)$ is a finite $\Gamma(V,U)$-module for every affine open $U$, `IsQuasicoherent` when for every affine open $U$ and $f \in \Gamma(V,U)$ every section over $V.basicOpen f$ becomes, after multiplication by some power of $f$, a restriction, and every section over $U$ restricting to $0$ is killed by a power of $f$, and `SupportedIn Y` for a closed $Y \subseteq V$ when $G(U)$ is trivial for every affine open $U$ disjoint from $Y$. Let $Q$ be a predicate on pairs (closed subset $Y$ of $V$, such a presheaf $G$) satisfying: (h0) $Q(Y,G)$ holds whenever $G(U)$ is a subsingleton for all affine opens $U$; (hmono) $Y' \le Y$ and $Q(Y',G)$ imply $Q(Y,G)$; (hext) for each $Y$ and each triple $G_1, G_2, G_3$ of coherent quasi-coherent presheaves admitting an `AffSES`, i.e. maps $G_1 \to G_2 \to G_3$ that are $R$-linear, $\Gamma(V,U)$-semilinear and natural on affine opens, with $G_1(U) \to G_2(U)$ injective, $G_2(U) \to G_3(U)$ surjective and exact in the middle for every affine open $U$, any two of $Q(Y,G_1), Q(Y,G_2), Q(Y,G_3)$ imply the third; (hInt) for every closed $Z_0$ with nonempty underlying set whose subscheme attached to the vanishing ideal sheaf of $Z_0$ is integral, if $Q(Y',G)$ holds for all $Y' < Z_0$ and all coherent quasi-coherent $G$ supported in $Y'$, then $Q(Z_0, \cdot)$ holds for the pushforward along the closed immersion $Z_0 \to V$ of the unit presheaf $U \mapsto \Gamma(Z_0,U)$. The conclusion is that $Q(Y,F)$ holds for every closed $Y \subseteq V$ and every coherent quasi-coherent $F$ supported in $Y$.
--
--   This is Grothendieck's dévissage principle for coherent sheaves on a proper scheme over a Noetherian base, in the support-indexed form: a property stable under trivial data, enlargement of the support and two-out-of-three in affine-locally exact sequences, and valid for structure sheaves of integral closed subschemes, holds for all coherent quasi-coherent data. It is the inductive engine behind the results on Euler characteristics of twists, used to show that $n \mapsto \chi(F \otimes L^{n})$ is a polynomial and to bound its degree by the dimension of the support.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_forall_coherent_of_forall_integral.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (Q : Closeds V → OModulePresheaf π → Prop)
    (h0 : ∀ (Y : Closeds V) (G : OModulePresheaf π), (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q Y G)
    (hmono : ∀ (Y Y' : Closeds V) (G : OModulePresheaf π), Y' ≤ Y → Q Y' G → Q Y G)
    (hext : ∀ (Y : Closeds V) (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent →
      (Q Y G₁ → Q Y G₃ → Q Y G₂) ∧ (Q Y G₁ → Q Y G₂ → Q Y G₃) ∧ (Q Y G₂ → Q Y G₃ → Q Y G₁))
    (hInt : ∀ Z₀ : Closeds V, (Z₀ : Set V).Nonempty →
      IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme →
      (∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q Y' G) →
      Q Z₀ (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι)) :
    ∀ (Y : Closeds V) (F : OModulePresheaf π), F.IsCoherent → F.IsQuasicoherent → F.SupportedIn Y → Q Y F := by sorry
