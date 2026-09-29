-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/05d61160-871e-5ca8-bbaf-609e03a06fc3
-- title:
--   Untwisting compatible generating sections over a projective A-scheme
-- statement:
--   Let $A$ be a commutative ring and $I \subseteq A$ an ideal, let $r \in \mathbb{N}$, and let $\iota : P \to \operatorname{Proj}$ of the homogeneous coordinate ring $A[x_0,\dots,x_r]$ be a closed immersion whose composite with the projection $\mathrm{ProjSpace.\pi}$ equals a separated morphism $q : P \to \operatorname{Spec} A$. Let $F_k$, $k \in \mathbb{N}$, be module data on $q$ (presheaves of $A$-modules with compatible $\Gamma(P,U)$-actions and restriction maps) that are coherent, i.e. $F_k(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasi-coherent in the sense that for every affine open $U$ and $f \in \Gamma(P,U)$ the restriction to the basic open of $f$ inverts $f$ in the usual two-sided sense. Let $\varphi_k : F_{k+1} \to F_k$ be maps given by $\Gamma$-linear maps on affine opens commuting with restriction, such that for every affine open $U$ the map $\varphi_k$ on $U$ is surjective with kernel $I^{k+1} \cdot F_{k+1}(U)$. Fix $d, m \in \mathbb{N}$ and, for every $k$, sections $\sigma_{k,1},\dots,\sigma_{k,m}$ in the degree-zero Čech kernel $H^0$ of the open-by-open tensor product $F_k \otimes \mathrm{ProjSpace.twist}\ q\ \iota\ d$ with respect to the ordered affine cover of $P$ by the preimages $\iota^{-1}(D_+(x_j))$ of the standard charts; assume that $\varphi_k \otimes \mathrm{id}$ carries $\sigma_{k+1,l}$ to $\sigma_{k,l}$ for all $k$ and $l$, and that for each index $s$ of the cover in degree $0$ the values $\sigma_{0,l}(s)$ span the module of sections of $F_0 \otimes \mathrm{ProjSpace.twist}\ q\ \iota\ d$ over the corresponding chart over its ring of functions. Then there exist module datum $E$ on $q$ and maps $\theta_k : E \to F_k$, given on affine opens, such that $E$ is coherent and quasi-coherent, each $\theta_k$ is surjective on every affine open, and $\varphi_k \circ \theta_{k+1} = \theta_k$ on every affine open. No further relation between $E$ and the data $d$, $m$, $\sigma$ is asserted.
--
--   This is the untwisting step in the construction of a coherent presentation of an $I$-adic system of coherent modules on a projective $A$-scheme: compatible global generating sections of the twists $F_k(d)$ are converted into a single coherent quasi-coherent datum surjecting compatibly onto all the $F_k$. It feeds the version of the statement in which the adic system is given only by the kernel condition $\ker \varphi_k = I^{k+1}F_{k+1}$ for a closed immersion into projective space.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafTensorMap
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_forall_surjective_of_forall_H0Map_tensorMap_eq_of_span_eq_top
    {A : Type u} [CommRing A] (I : Ideal A)
    {r : ℕ} {P : Scheme.{u}} (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A))
    [IsClosedImmersion ι] {q : P ⟶ Spec (CommRingCat.of A)} (hιq : ι ≫ ProjSpace.π A r = q) [IsSeparated q]
    (F : ℕ → OModulePresheaf q) (hc : ∀ k, (F k).IsCoherent) (hq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (d m : ℕ)
    (σ : ∀ k : ℕ, Fin m → ↥(((F k).tensor (ProjSpace.twist q ι d)).H0 (ProjSpace.stdCoverPullback ι)))
    (hσ : ∀ (k : ℕ) (l : Fin m),
      (OModulePresheaf.AffHom.tensorMap (φ k) (OModulePresheaf.AffHom.id (ProjSpace.twist q ι d))).H0Map
        (ProjSpace.stdCoverPullback ι) (σ (k + 1) l) = σ k l)
    (hgen : ∀ s : (ProjSpace.stdCoverPullback ι).Idx 0,
      Submodule.span Γ(P, (ProjSpace.stdCoverPullback ι).inter s)
          (Set.range fun l : Fin m =>
            (σ 0 l : ((F 0).tensor (ProjSpace.twist q ι d)).cochain (ProjSpace.stdCoverPullback ι) 0) s) = ⊤) :
    ∃ (E : OModulePresheaf q) (θ : ∀ k, OModulePresheaf.AffHom E (F k)),
      E.IsCoherent ∧ E.IsQuasicoherent ∧
      (∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((θ k).app U)) ∧
      (∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (θ (k + 1)).app U = (θ k).app U) := by sorry
