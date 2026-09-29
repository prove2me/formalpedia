-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral
-- name    : AlgebraicGeometry.OModulePresheaf.forall_pushforward_of_isIntegral
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/7a2c420f-6cc0-5171-ba81-96c1f1d7eea1
-- title:
--   Dévissage step along an integral closed subscheme
-- statement:
--   Let $R$ be a Noetherian commutative ring, $V$ a scheme, and $\pi : V \to \operatorname{Spec} R$ a proper morphism. Let $Z_0$ be a closed subset of $V$ with nonempty underlying set, write $\iota$ for the closed immersion of the subscheme cut out by the vanishing ideal sheaf of $Z_0$, and assume that subscheme is integral. Let $Q$ be a predicate on the $\mathcal{O}$-module presheaves over $\pi$, that is, on data assigning to each open $U \subseteq V$ an abelian group that is a module over $R$ and over $\Gamma(V,U)$, compatibly via the $R$-algebra structure on $\Gamma(V,U)$ coming from $\pi$, together with $R$-linear restriction maps for $U \le U'$ that are semilinear for restriction of functions, reflexive and transitive. Assume: $Q(G)$ holds whenever $G$ has subsingleton sections over every affine open; for all $G_1,G_2,G_3$ admitting an affine-open short exact sequence (a pair of maps given over each affine open by $R$-linear, $\Gamma(V,U)$-semilinear maps commuting with restriction, the first injective, the second surjective, with range of the first equal to the kernel of the second, over every affine open) and all coherent, i.e. with $\Gamma(V,U)$-module-finite sections over affine opens, and quasi-coherent, i.e. satisfying the basic-open conditions that every section over $V.\mathrm{basicOpen}\,f$ becomes, after multiplication by some power of $f$, a restriction from $U$, and every section over $U$ restricting to $0$ there is killed by a power of $f$, any two of $Q(G_1), Q(G_2), Q(G_3)$ imply the third; $Q$ holds for the pushforward along $\iota$ of the unit presheaf $U \mapsto \Gamma(Z_0, \iota^{-1}U)$; and $Q(G)$ holds for every coherent quasi-coherent $G$ supported in a closed $Y' < Z_0$, support meaning subsingleton sections over affine opens meeting $Y'$ trivially. Then, for every $\mathcal{O}$-module presheaf $H$ over $\iota$ followed by $\pi$ whose pushforward $U \mapsto H(\iota^{-1}U)$ along $\iota$ is coherent, quasi-coherent and supported in $Z_0$, the conclusion $Q$ holds for that pushforward.
--
--   This is the pivotal step of Grothendieck's dévissage: it reduces a two-out-of-three property of coherent quasi-coherent data to the structure sheaf of an integral closed subscheme together with data supported in strictly smaller closed subsets. It is invoked in the induction [`AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_coherent_of_forall_integral), and its own input is the generic freeness statement [`AlgebraicGeometry.OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_basicOpen_sections_free_of_isIntegral).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_forall_pushforward_of_isIntegral.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafConstructions

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

theorem AlgebraicGeometry.OModulePresheaf.forall_pushforward_of_isIntegral
    {R : Type u} [CommRing R] [IsNoetherianRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) [IsProper π]
    (Z₀ : Closeds V) (hZ₀ : (Z₀ : Set V).Nonempty)
    (hint : IsIntegral (Scheme.IdealSheafData.vanishingIdeal Z₀).subscheme)
    (Q : OModulePresheaf π → Prop)
    (h0 : ∀ G : OModulePresheaf π, (∀ U : V.affineOpens, Subsingleton (G.obj U.1)) → Q G)
    (hext : ∀ (G₁ G₂ G₃ : OModulePresheaf π), Nonempty (OModulePresheaf.AffSES G₁ G₂ G₃) →
      G₁.IsCoherent → G₁.IsQuasicoherent → G₂.IsCoherent → G₂.IsQuasicoherent →
      G₃.IsCoherent → G₃.IsQuasicoherent →
      (Q G₁ → Q G₃ → Q G₂) ∧ (Q G₁ → Q G₂ → Q G₃) ∧ (Q G₂ → Q G₃ → Q G₁))
    (hO : Q (OModulePresheaf.pushforwardUnit π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι))
    (ih : ∀ Y' < Z₀, ∀ G : OModulePresheaf π, G.IsCoherent → G.IsQuasicoherent → G.SupportedIn Y' → Q G)
    (H : OModulePresheaf ((Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι ≫ π))
    (hc : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsCoherent)
    (hq : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).IsQuasicoherent)
    (hs : (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H).SupportedIn Z₀) :
    Q (OModulePresheaf.pushforward π (Scheme.IdealSheafData.vanishingIdeal Z₀).subschemeι H) := by sorry
