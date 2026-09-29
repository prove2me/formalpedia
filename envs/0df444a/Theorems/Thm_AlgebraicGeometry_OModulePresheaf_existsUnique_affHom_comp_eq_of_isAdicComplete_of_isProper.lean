-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
-- name    : AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/f310b7ed-d2b0-55ee-a17b-8aada32b27fd
-- title:
--   Unique lifting of compatible maps F → mathcal Gₙ to G
-- statement:
--   Let $R$ be a Noetherian commutative ring, $I \subseteq R$ an ideal for which $R$ is $I$-adically complete, $X$ a scheme and $f : X \to \operatorname{Spec} R$ a proper morphism. Let $F$ and $G$ be module-presheaf data over $f$: each assigns to every open $U \subseteq X$ an abelian group carrying an $R$-module and a $\Gamma(X,U)$-module structure compatible via the algebra map $R \to \Gamma(X,U)$ determined by $f$, together with $R$-linear restriction maps that are semilinear for restriction of sections and satisfy the identity and transitivity laws. Assume $F$ and $G$ are coherent, i.e. their sections over every affine open $U$ form a finite $\Gamma(X,U)$-module, and quasi-coherent, i.e. for every affine open $U$ and every $a \in \Gamma(X,U)$ each section over the basic open $D(a)$ becomes, after multiplication by some power of $a$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $D(a)$ is annihilated by some power of $a$. Let $G_n$ ($n \in \mathbb N$) be further such data, with morphisms $\tau_n : G_{n+1} \to G_n$ and $\rho_n : G \to G_n$, where a morphism consists of $R$-linear maps on sections over affine opens that are semilinear for multiplication by sections and commute with restriction between affine opens. Assume each $\rho_n$ is surjective on every affine open $U$ with kernel $I^{n+1} \cdot G(U)$ (the $R$-submodule generated), and $\tau_n \circ \rho_{n+1} = \rho_n$. Then for every family of morphisms $\psi_n : F \to G_n$ with $\tau_n \circ \psi_{n+1} = \psi_n$ there is a morphism $\varphi : F \to G$ with $\rho_n \circ \varphi = \psi_n$ for all $n$, and any morphism with this property equals $\varphi$.
--
--   This is the degree-zero case of Grothendieck's theorem on formal functions in the form asserting that $\operatorname{Hom}(\mathcal F, \mathcal G)$ is $I$-adically complete for coherent data on a proper $R$-scheme, so that compatible systems of maps into the truncations $\mathcal G/I^{n+1}\mathcal G$ come from a unique map into $\mathcal G$. It is used in the construction of morphisms and of coherent quotients with prescribed kernels $I^{n+1}\cdot(-)$ in the formal–algebraic comparison results that follow.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

theorem AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper
    {R : Type u} [CommRing R] [IsNoetherianRing R] (I : Ideal R) [IsAdicComplete I R]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f]
    (F G : OModulePresheaf f)
    (hFc : F.IsCoherent) (hFq : F.IsQuasicoherent) (hGc : G.IsCoherent) (hGq : G.IsQuasicoherent)
    (Gn : ℕ → OModulePresheaf f) (τ : ∀ n : ℕ, OModulePresheaf.AffHom (Gn (n + 1)) (Gn n))
    (ρ : ∀ n : ℕ, OModulePresheaf.AffHom G (Gn n))
    (hρs : ∀ (n : ℕ) (U : X.affineOpens), Function.Surjective ((ρ n).app U))
    (hρk : ∀ (n : ℕ) (U : X.affineOpens),
      LinearMap.ker ((ρ n).app U) = I ^ (n + 1) • (⊤ : Submodule R (G.obj U.1)))
    (hρc : ∀ n : ℕ, (τ n).comp (ρ (n + 1)) = ρ n)
    (ψ : ∀ n : ℕ, OModulePresheaf.AffHom F (Gn n)) (hψ : ∀ n : ℕ, (τ n).comp (ψ (n + 1)) = ψ n) :
    ∃ φ : OModulePresheaf.AffHom F G, (∀ n : ℕ, (ρ n).comp φ = ψ n) ∧
      ∀ φ' : OModulePresheaf.AffHom F G, (∀ n : ℕ, (ρ n).comp φ' = ψ n) → φ' = φ := by sorry
