-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback
-- name    : AlgebraicGeometry.ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/bf5b9eb6-7aad-5c61-85f1-2ceeaddeda4b
-- title:
--   Base change of the Čech complex of the twist mathcal O_Z(d)
-- statement:
--   Let $A$ be a commutative ring, $n$ a natural number, $Z$ a scheme and $\iota : Z \to \mathbb P^n_A = \operatorname{Proj}$ of the graded algebra of homogeneous components of $A[x_0,\dots,x_n]$ an affine morphism; let $B$ be an $A$-algebra, $Z'$ a scheme and $\iota' : Z' \to \mathbb P^n_B$ an affine morphism; let $e : Z' \to Z$ be a morphism such that the square formed by $e$, the structure morphism $Z' \to \mathbb P^n_B \to \operatorname{Spec} B$, the structure morphism $Z \to \mathbb P^n_A \to \operatorname{Spec} A$ and $\operatorname{Spec}(A \to B)$ is cartesian, and such that $\iota \circ e = \mathbb P^n_B \to \mathbb P^n_A$ followed by nothing else, i.e. $\iota \circ e$ equals $\iota'$ followed by `ProjSpace.map A B n`. Fix $d : \mathbb N$. Here `ProjSpace.stdCoverPullback ι` is the ordered affine cover of $Z$ indexed by (a `ULift` of) $\{0,\dots,n\}$ with $j$-th member $\iota^{-1}D_+(x_j)$, affine because $\iota$ is, and likewise for $\iota'$; for a strictly monotone $s : \{0,\dots,i\} \to \{0,\dots,n\}$ the open `inter s` is the intersection of the $\iota^{-1}D_+(x_{s_k})$, and the level-$i$ cochains of the degree-$d$ twist presheaf `ProjSpace.twist` are the families, indexed by such $s$, of sections of that presheaf over `inter s`, a section over an open $U$ being given by components `val j` in $\Gamma(Z, U \sqcap \iota^{-1}D_+(x_j))$. The assertion is that there exists a family of $B$-linear isomorphisms $\varepsilon_i : B \otimes_A \check C^i_A \to \check C^i_B$ between the base change to $B$ of the level-$i$ cochains for $(\iota, A)$ and the level-$i$ cochains for $(\iota', B)$, such that (i) for every $i$, $\varepsilon_{i+1}$ composed with the $B$-base change of the $i$-th differential of the $A$-side complex equals the $i$-th differential of the $B$-side complex composed with $\varepsilon_i$, and (ii) for every $i$, every $A$-side cochain $c$, every index $s$ (the two covers share the same index set, hence the same index types), every $j \in \{0,\dots,n\}$ and every proof $h$ that $\mathrm{inter}'(s) \sqcap \iota'^{-1}D_+(x_j) \le e^{-1}(\mathrm{inter}(s) \sqcap \iota^{-1}D_+(x_j))$, the $j$-th component of $\varepsilon_i(1 \otimes c)$ at $s$ is the restriction along $h$ of the pull-back under $e$ of the $j$-th component of $c(s)$.
--
--   This is the statement that the alternating Čech complex of $\mathcal O_Z(d)$ on the standard charts $\iota^{-1}D_+(x_j)$ commutes with base change $A \to B$ along a cartesian realisation of $Z_B$ inside $\mathbb P^n_B$, in the explicit form in which the comparison maps are pull-back of functions along $e$. It underlies the finiteness and base-change statements for $H^0$ of twists and the construction of the Hilbert functor's local data, being cited by [`AlgebraicGeometry.ProjSpace.finite_projective_H0_twist_of_ker_baseChange_of_isPullback`](thm.html#AlgebraicGeometry.ProjSpace.finite_projective_H0_twist_of_ker_baseChange_of_isPullback) and by the Hilbert-functor lemmas on closed immersions that are flat over the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_linearEquiv_baseChange_cochain_twist_of_isPullback.lean

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

theorem AlgebraicGeometry.ProjSpace.exists_linearEquiv_baseChange_cochain_twist_of_isPullback
    {A : Type u} [CommRing A] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A)) [IsAffineHom ι]
    (B : Type u) [CommRing B] [Algebra A B] {Z' : Scheme.{u}}
    (ι' : Z' ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) B)) [IsAffineHom ι']
    (e : Z' ⟶ Z)
    (hpb : IsPullback e (ι' ≫ ProjSpace.π B n) (ι ≫ ProjSpace.π A n) (Spec.map (CommRingCat.ofHom (algebraMap A B))))
    (hcomp : e ≫ ι = ι' ≫ ProjSpace.map A B n) (d : ℕ) :
    ∃ ε : ∀ i : ℕ,
        B ⊗[A] (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i ≃ₗ[B]
          (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).cochain (ProjSpace.stdCoverPullback ι') i,
      (∀ i : ℕ,
        (ε (i + 1)).toLinearMap ∘ₗ ((ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).d (ProjSpace.stdCoverPullback ι) i).baseChange B =
          (ProjSpace.twist (ι' ≫ ProjSpace.π B n) ι' d).d (ProjSpace.stdCoverPullback ι') i ∘ₗ (ε i).toLinearMap) ∧
      (∀ (i : ℕ) (c : (ProjSpace.twist (ι ≫ ProjSpace.π A n) ι d).cochain (ProjSpace.stdCoverPullback ι) i)
        (s : (ProjSpace.stdCoverPullback ι).Idx i) (j : Fin (n + 1))
        (h : (ProjSpace.stdCoverPullback ι').inter s ⊓ ProjSpace.pullbackChart ι' j ≤
          e ⁻¹ᵁ ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)),
        (ε i ((1 : B) ⊗ₜ[A] c) s).val j =
          ProjSpace.restrictFun h ((e.app ((ProjSpace.stdCoverPullback ι).inter s ⊓ ProjSpace.pullbackChart ι j)) ((c s).val j))) := by sorry
