-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
-- name    : AlgebraicGeometry.OModulePresheaf.exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/361ead40-7ee1-566a-b135-a6d1178f0d2c
-- title:
--   Extending sections from chart intersections to compatible twisted frame families
-- statement:
--   Let $A$ be a commutative ring, $r,i,d\in\mathbb N$, and let $\iota : P \to \operatorname{Proj}$ of the homogeneous-submodule grading on $A[x_0,\dots,x_r]$ be an affine morphism of schemes; write $U_j = \iota^{-1}D_+(x_j)$ for the pulled-back standard charts (`ProjSpace.pullbackChart`) and $u_{jl} = \iota^{\sharp}(x_l/x_j) \in \Gamma(P, U_j)$ for the frame units (`ProjSpace.frameUnit`, the image under $\iota$ of the section of the $D_+(x_j)$-affine chart given by the degree-zero ratio $x_l/x_j$). Let $q : P \to \operatorname{Spec} A$ be a morphism and $G$ an $\mathcal O$-module datum over $q$: an assignment of an $A$-module and $\Gamma(P,U)$-module $G(U)$ to each open $U$, with restriction $A$-linear maps compatible with scalar restriction, reflexive and transitive. Assume $G$ is quasi-coherent in the sense that for every affine open $U$ and every $f \in \Gamma(P,U)$, each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and every section over $U$ restricting to $0$ on $D(f)$ is killed by a power of $f$. Given chart indices $c : \mathrm{Fin}(i+1) \to \mathrm{Fin}(r+1)$ and $t \in G(W)$ with $W = \bigcap_v U_{c_v}$, the conclusion asserts the existence of $N \in \mathbb N$ and sections $t'_j \in G(U_j)$ for all $j$ such that: (i) $t'$ satisfies the frame compatibility of degree $d + N(i+1)$, i.e. on $U_j \cap U_l$ one has $t'_j| = (u_{jl}|)^{\,d+N(i+1)} \cdot t'_l|$ for all $j,l$; and (ii) for every $j$, the restriction of $t'_j$ to $U_j \cap W$ equals $\bigl(\prod_{v} u_{j c_v}|\bigr)^{N}\,(u_{j c_0}|)^{d}$ times the restriction of $t$ to $U_j \cap W$.
--
--   This is the frame-wise form of Hartshorne's extension lemma II.5.14(b) for the present notion of quasi-coherent module datum on a scheme affine over $\mathbb P^r_A$: a section over an intersection of charts, twisted by $x_{c_0}^d$, extends to a global section of the twist by $d + N(i+1)$ after multiplication by the $N$-th power of $x_{c_0}\cdots x_{c_i}$. It is used in the construction of a finitely generated graded module mapping into the family of frame-compatible sections, and in the vanishing statement for the twisted shifted cohomology of that graded module.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafFamilyFramesGradedModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.OModulePresheaf.exists_framesCompat_res_eq_prod_frameUnit_pow_smul_res_of_isQuasicoherent
    {A : Type u} [CommRing A] {r : ℕ} {P : Scheme.{u}}
    (ι : P ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (r + 1)) A)) [IsAffineHom ι]
    {q : P ⟶ Spec (CommRingCat.of A)} (G : OModulePresheaf q) (hq : G.IsQuasicoherent)
    {i : ℕ} (c : Fin (i + 1) → Fin (r + 1)) (d : ℕ) (t : G.obj (⨅ v, ProjSpace.pullbackChart ι (c v))) :
    ∃ (N : ℕ) (t' : ∀ j : Fin (r + 1), G.obj (ProjSpace.pullbackChart ι j)),
      OModulePresheaf.FramesCompat ι G (d + N * (i + 1)) t' ∧
      ∀ j : Fin (r + 1),
        G.res (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
            (t' j) =
          ((∏ v : Fin (i + 1), ProjSpace.restrictFun
                (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
                (ProjSpace.frameUnit ι j (c v))) ^ N *
              ProjSpace.restrictFun
                (inf_le_left : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ProjSpace.pullbackChart ι j)
                (ProjSpace.frameUnit ι j (c 0)) ^ d) •
            G.res (inf_le_right : ProjSpace.pullbackChart ι j ⊓ ⨅ v, ProjSpace.pullbackChart ι (c v) ≤ ⨅ v, ProjSpace.pullbackChart ι (c v)) t := by sorry
