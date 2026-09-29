-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_locallyOfFiniteType_of_quotient_of_isNoetherianRing
-- name    : AlgebraicGeometry.Scheme.locallyOfFiniteType_of_quotient_of_isNoetherianRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.322128+00:00
-- url     : https://prove2.me/theorems/05fcd2f0-eac8-5f65-9622-086e08f1e447
-- title:
--   Finite quotients of locally finite type schemes over a noetherian base
-- statement:
--   Let $\mathcal O$ be a noetherian commutative ring and let $M$, $X$ be schemes, with structure morphisms $f_M : M \to \operatorname{Spec}\mathcal O$ and $f : X \to \operatorname{Spec}\mathcal O$, where $f_M$ is locally of finite type. Let $G$ be a finite group acting on $M$ through a homomorphism $\rho : G \to \operatorname{Aut} M$, and let $p : M \to X$ be a morphism with $p$ followed by $f$ equal to $f_M$ and with $\rho(g)$ followed by $p$ equal to $p$ for every $g \in G$. Assume further that $p$ is an integral morphism, an affine morphism, and surjective on underlying points; that for every open $V \subseteq X$ the map on sections $\Gamma(X,V) \to \Gamma(M, p^{-1}V)$ induced by $p$ is injective; that its image consists exactly of those sections of $\mathcal O_M$ over $p^{-1}V$ fixed by the automorphisms induced by all $\rho(g)$ on $p^{-1}V$ (which is $\rho(g)$-stable by $G$-invariance of $p$); and that every affine open $U \subseteq M$ with $\rho(g)^{-1}U = U$ for all $g$ is of the form $p^{-1}V$ for some affine open $V \subseteq X$. Then $f$ is locally of finite type.
--
--   This is the statement that a quotient of a scheme locally of finite type over a noetherian base by a finite group action, presented by the invariant-sections and affine-descent clauses of the finite-group quotient construction, is again locally of finite type; the underlying ring-theoretic content is of Artin–Tate type. It is used in the Čerednik–Drinfeld comparison, where the coarse and fine moduli quotients over the relevant base must be known to be locally of finite type.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_locallyOfFiniteType_of_quotient_of_isNoetherianRing.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.Scheme.locallyOfFiniteType_of_quotient_of_isNoetherianRing
    {𝒪 : Type} [CommRing 𝒪] [IsNoetherianRing 𝒪]
    {M X : Scheme.{0}} (fM : M ⟶ Spec (CommRingCat.of 𝒪)) (f : X ⟶ Spec (CommRingCat.of 𝒪)) (hlft : LocallyOfFiniteType fM)
    {G : Type} [Group G] [Finite G] (ρ : G →* Aut M)
    (p : M ⟶ X) (hp : p ≫ f = fM) (hρp : ∀ g : G, (ρ g).hom ≫ p = p)
    (hint : IsIntegralHom p) (haff : IsAffineHom p) (hsurj : Function.Surjective p.base)
    (hsec : ∀ V : X.Opens, Function.Injective (p.app V))
    (hinv : ∀ V : X.Opens, Set.range (p.app V) =
      {s | ∀ g : G, (ρ g).hom.appLE (p ⁻¹ᵁ V) (p ⁻¹ᵁ V) (by rw [← Scheme.Hom.comp_preimage, hρp g]) s = s})
    (hopen : ∀ U : M.Opens, IsAffineOpen U → (∀ g : G, (ρ g).hom ⁻¹ᵁ U = U) → ∃ V : X.Opens, IsAffineOpen V ∧ p ⁻¹ᵁ V = U) :
    LocallyOfFiniteType f := by sorry
