-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_isHomogeneous_of_baseChange_field
-- name    : AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_isHomogeneous_of_baseChange_field
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/2702bb2e-7054-51e8-8fa5-8d88de45f01f
-- title:
--   Field descent of representability of twist Čech 0-cocycles
-- statement:
--   Fix a field $k$, a natural number $n$, a scheme $Z$ and an affine morphism $\iota : Z \to \operatorname{Proj}$ of the graded ring of homogeneous components of $k[x_0,\dots,x_n]$, i.e. $\iota : Z \to \mathbb{P}^n_k$. Let $K$ be a field that is a $k$-algebra, let $\iota' : Z' \to \mathbb{P}^n_K$ be affine, and let $e : Z' \to Z$ be a morphism such that the square formed by $e$, the structure morphism $\iota'$ followed by $\pi_K$, the structure morphism $\iota$ followed by $\pi_k$, and $\operatorname{Spec}$ of $k \to K$ is a pullback, and such that $e$ followed by $\iota$ equals $\iota'$ followed by the morphism $\mathbb{P}^n_K \to \mathbb{P}^n_k$ induced by coefficient extension. Fix $d \in \mathbb{N}$. The covers used are the preimages under $\iota$ (resp. $\iota'$) of the $n+1$ standard charts, an ordered affine cover indexed by $\mathrm{ULift}(\mathrm{Fin}(n+1))$, and the coefficient module is the twist datum of degree $d$ attached to $\iota$ (resp. $\iota'$) over $\operatorname{Spec} k$ (resp. $\operatorname{Spec} K$). The hypothesis is that over $K$ every element $c$ of the kernel $H^0$ of the Čech differential on $0$-cochains — that is, every family of sections over the intersections $\bigsqcap_j U_{s(j)}$ indexed by strictly monotone $s : \mathrm{Fin}\,1 \to$ the index type — is represented by a single homogeneous polynomial: there are $F \in K[x_0,\dots,x_n]$ and a proof that $F$ is homogeneous of degree $d$ such that for all $s$ and all $i$, the $i$-th component $(c\,s).\mathrm{val}\,i$ is the restriction to $\bigsqcap_j U_{s(j)} \cap \iota'^{-1}D(x_i)$ of the pullback along $\iota'$ of the section of $\mathcal{O}_{\mathbb{P}^n_K}$ on $D(x_i)$ given by the homogeneous localisation $F/x_i^d$. The conclusion is the same assertion over $k$, with $F \in k[x_0,\dots,x_n]$, for $\iota$ and its pulled-back standard cover.
--
--   This is the descent along a field extension of the statement that the comparison map from degree-$d$ forms to Čech $0$-cocycles of the degree-$d$ twist datum is surjective, obtained from flat base change for the Čech complex together with faithful flatness of $k \to K$. It serves as one half of the base-change step in the cohomological regularity estimates used by [`AlgebraicGeometry.HilbertFunctor.exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_forall_H0_twist_exists_isHomogeneous_of_baseChange_field.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_isHomogeneous_of_baseChange_field
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsAffineHom ι]
    (K : Type u) [Field K] [Algebra k K] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π K n) (ι ≫ ProjSpace.π k n) (Spec.map (CommRingCat.ofHom (algebraMap k K))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map k K n) (d : ℕ)
    (hK : ∀ c ∈ (ProjSpace.twist (ι' ≫ ProjSpace.π K n) ι' d).H0 (ProjSpace.stdCoverPullback ι'),
        ∃ (F : MvPolynomial (Fin (n + 1)) K) (hF : F.IsHomogeneous d),
          ∀ (s : (ProjSpace.stdCoverPullback ι').Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' i ≤
                    ProjSpace.pullbackChart ι' i)
                  (ι'.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) K) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) :
    ∀ c ∈ (ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).H0 (ProjSpace.stdCoverPullback ι),
        ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
          ∀ (s : (ProjSpace.stdCoverPullback ι).Idx 0) (i : Fin (n + 1)),
            (c s).val i =
              ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι i ≤
                    ProjSpace.pullbackChart ι i)
                  (ι.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) := by sorry
