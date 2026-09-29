-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth
-- name    : AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/22bbc5ae-23b4-50a3-9ce8-6e2434716888
-- title:
--   Čech acyclicity and surjectivity for ideals of maximal growth
-- statement:
--   Let $n,m$ be natural numbers with $m \ge 1$, let $k$ be an infinite field, and let $J$ be an ideal of $S = k[x_0,\dots,x_n]$ which is the span of a set of forms all of degree $m$. Assume maximal growth: $\dim_k \mathrm{piece}\,J\,(m+1) = \mathrm{Nat.macaulayPow}\;m\;(\dim_k \mathrm{piece}\,J\,m)$, where $\mathrm{piece}\,J\,d$ is the degree-$d$ homogeneous part of $S$ modulo its intersection with $J$, and [`Nat.macaulayPow`](def/Nat_MacaulayPow.html#L7) is the recursively defined Macaulay operation $a \mapsto a^{\langle m\rangle}$ given by the binomial expansion. Let $\iota_k : Z_k \to \mathrm{Proj}\,S$ be a closed immersion such that for every $d \ge m$ and every form $F$ of degree $d$, one has $F \in J$ if and only if, for each $i$, the section of $\mathcal O_{Z_k}$ obtained by pulling back $F/x_i^d$ along $\iota_k$ over the chart $D_+(x_i)$ vanishes. The conclusion is that for every $d \ge m$: first, for all $i$, the $i$-th higher Čech cohomology $\mathrm{HSucc}\,i$ (the quotient of $\ker d^{i+1}$ by the image of $d^i$) of the twist datum `ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d` with respect to the pullback of the standard affine cover is a subsingleton; second, every $c$ in its $H^0$ (the kernel of the differential on $0$-cochains) arises from a form $F$ of degree $d$, in the sense that for each cover index $s$ and each $i$, the $i$-th component of $c\,s$ is the restriction to $\mathrm{inter}\,s \sqcap \mathrm{pullbackChart}\,\iota_k\,i$ of the pullback of $F/x_i^d$.
--
--   This is Gotzmann's regularity statement for an ideal generated in degree $m$ with maximal growth, expressed in the Čech currency of the twist data on the pulled-back standard cover of $\mathbb P^n_k$: vanishing of all higher Čech groups together with surjectivity of degree-$d$ forms onto global sections, for all $d \ge m$. It feeds the uniform bound for Hilbert-functor arguments, being cited by [`AlgebraicGeometry.HilbertFunctor.exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf`](thm.html#AlgebraicGeometry.HilbertFunctor.exists_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_point_hilbertFunctionOf).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_HilbertFunctor
import Definitions.Def_Nat_MacaulayPow

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial AlgebraicGeometry.HilbertFunctor

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth
    (n m : ℕ) (hm : 1 ≤ m) (k : Type) [Field k] [Infinite k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k))
    (hJ : ∃ s : Set (MvPolynomial (Fin (n + 1)) k), (∀ p ∈ s, p.IsHomogeneous m) ∧ J = Ideal.span s)
    (hmax : Module.finrank k (piece J (m + 1)) = Nat.macaulayPow m (Module.finrank k (piece J m)))
    (Zk : Scheme.{0}) (ιk : Zk ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ιk]
    (hZ : (∀ (d : ℕ), m ≤ d → ∀ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
        (F ∈ J ↔ ∀ i : Fin (n + 1), (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ }))) = 0))) :
    ∀ d : ℕ, m ≤ d →
      (∀ i : ℕ, Subsingleton
          ((ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).HSucc (ProjSpace.stdCoverPullback ιk) i)) ∧
      (∀ c ∈ (ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d).H0 (ProjSpace.stdCoverPullback ιk),
          ∃ (F : MvPolynomial (Fin (n + 1)) k) (hF : F.IsHomogeneous d),
            ∀ (s : (ProjSpace.stdCoverPullback ιk).Idx 0) (i : Fin (n + 1)),
              (c s).val i =
                ProjSpace.restrictFun
                  (inf_le_right : (ProjSpace.stdCoverPullback ιk).inter s ⊓ ProjSpace.pullbackChart ιk i ≤
                    ProjSpace.pullbackChart ιk i)
                  (ιk.app (Proj.basicOpen (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i))
              (Proj.awayToSection (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k) (MvPolynomial.X i)
                (HomogeneousLocalization.mk
                  { deg := d
                    num := ⟨F, (MvPolynomial.mem_homogeneousSubmodule d F).mpr hF⟩
                    den := ⟨MvPolynomial.X i ^ d, (MvPolynomial.mem_homogeneousSubmodule d _).mpr
                      (MvPolynomial.isHomogeneous_X_pow i d)⟩
                    den_mem := ⟨d, rfl⟩ })))) := by sorry
