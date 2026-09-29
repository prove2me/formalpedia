-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/45af8953-f2f7-5107-8cee-1a23e74eabbf
-- title:
--   Grothendieck existence for closed subschemes of P^r_A
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal with $A$ complete and separated for the $I$-adic topology, $r$ a natural number, and $\iota : P \to \operatorname{Proj}$ of the graded algebra of homogeneous components of $A[X_0,\dots,X_r]$ a closed immersion, with $q : P \to \operatorname{Spec} A$ such that $\iota$ followed by the structure morphism $\mathrm{ProjSpace}.\pi$ equals $q$. Here a datum `OModulePresheaf q` assigns to each open $U \subseteq P$ a module over $A$ and over $\Gamma(P,U)$, compatibly, together with $A$-linear restriction maps satisfying semilinearity, reflexivity and transitivity; it is coherent when each value on an affine open $U$ is a finite $\Gamma(P,U)$-module, and quasi-coherent when for every affine open $U$ and $f \in \Gamma(P,U)$ each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$; an `AffHom` is a family of $A$-linear maps on affine opens, semilinear for the sections and compatible with restrictions. Given a sequence $F_k$ of coherent quasi-coherent data with `AffHom`s $\varphi_k : F_{k+1} \to F_k$ whose components on every affine open $U$ are surjective with kernel $I^{k+1} \cdot F_{k+1}(U)$, the conclusion asserts the existence of a coherent quasi-coherent datum $G$ and `AffHom`s $\psi_k : G \to F_k$ whose components on every affine open $U$ are surjective with kernel $I^{k+1} \cdot G(U)$, and which satisfy $\varphi_k \circ \psi_{k+1} = \psi_k$ on every affine open.
--
--   This is the essential-surjectivity half of Grothendieck's existence theorem in formal geometry (EGA III₁, (5.2.4)–(5.2.5)) in the projective case: every $I$-adic system of coherent modules on a closed subscheme of $\mathbb{P}^r_A$ is the system of reductions of a single coherent module, the matching full faithfulness being [`AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper`](thm.html#AlgebraicGeometry.OModulePresheaf.existsUnique_affHom_comp_eq_of_isAdicComplete_of_isProper). It is the projective input to the version for arbitrary proper $q$, and is used in the constructions of ideal sheaf data with prescribed adic thickenings and of algebraisations of formal finite morphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_ProjSpace

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_ker_eq_pow_smul_top_of_isClosedImmersion_proj_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (G : OModulePresheaf q) (ψ : ∀ k, OModulePresheaf.AffHom G (F k)),
      G.IsCoherent ∧ G.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens),
        LinearMap.ker ((ψ k).app U) = I ^ (k + 1) • (⊤ : Submodule A (G.obj U.1))) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (ψ (k + 1)).app U = (ψ k).app U) := by sorry
