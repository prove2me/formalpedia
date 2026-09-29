-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/7109d789-b279-5a0b-a58d-3bc2c3ac59a7
-- title:
--   An I-adic system of coherent data is a quotient of one coherent datum
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, $r$ a natural number, $P$ a scheme, and $\iota : P \to \operatorname{Proj}$ of the graded ring of homogeneous polynomials in $r+1$ variables over $A$ a closed immersion; let $q : P \to \operatorname{Spec} A$ be a morphism with $\iota$ followed by the structure morphism $\pi$ of projective $r$-space equal to $q$. Let $F$ be a sequence of `OModulePresheaf q`, i.e. for each $k$ a family of $A$-modules $(F k)(U)$ indexed by the opens $U$ of $P$, each also a $\Gamma(P,U)$-module compatibly with the $A$-action through $q$, together with $A$-linear restriction maps satisfying the semilinearity, reflexivity and composition laws. Assume each $F k$ is coherent, meaning $(F k)(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent, meaning that for every affine open $U$ and $f \in \Gamma(P,U)$ every section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and every section over $U$ restricting to $0$ on $D(f)$ is killed by some power of $f$. Let $\varphi_k$ be, for each $k$, an `AffHom` from $F(k+1)$ to $F k$: a family of $A$-linear maps on affine opens, $\Gamma(P,U)$-semilinear and commuting with restriction along inclusions of affine opens. Assume each $(\varphi_k)_U$ is surjective with kernel $I^{k+1} \cdot (F(k+1))(U)$ for every affine open $U$. Then there exist a single `OModulePresheaf q`-datum $E$, coherent and quasi-coherent, and `AffHom`s $\theta_k : E \to F k$ that are surjective on every affine open and satisfy $(\varphi_k)_U \circ (\theta_{k+1})_U = (\theta_k)_U$ for all $k$ and all affine opens $U$.
--
--   This is the uniform generation step in Grothendieck's existence theorem for projective schemes (EGA III₁, (5.2.3), as used in the proof of (5.2.4)): an $I$-adic system of coherent sheaves on a closed subscheme of $\mathbb{P}^r_A$ is simultaneously a quotient of one coherent sheaf, which may be taken to be a direct sum of copies of a single sufficiently negative twist. It feeds the construction of an $I$-adically complete coherent module with prescribed reductions, used in the algebraisation arguments of the deformation-theoretic part of the project.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion.lean

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

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_ker_eq_pow_smul_top_of_isClosedImmersion
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q)
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1))) :
    ∃ (E : OModulePresheaf q) (θ : ∀ k, OModulePresheaf.AffHom E (F k)),
      E.IsCoherent ∧ E.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U) := by sorry
