-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero
-- name    : AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/85048377-32a3-5b10-915e-9280132b314b
-- title:
--   Vanishing degree-m piece forces trivial twisted Čech groups
-- statement:
--   Fix natural numbers $n,m$, a field $k$ (in the bottom universe) and an ideal $J$ of $k[X_0,\dots,X_n]$, and assume that `piece J m` — the quotient of the $k$-space of homogeneous polynomials of degree $m$ by its intersection with $J$ — has finrank $0$ over $k$. Let $Z$ be a scheme and $\iota : Z \to \operatorname{Proj}$ of the graded ring $k[X_0,\dots,X_n]$ a closed immersion, and assume the chartwise comparison hypothesis `hZ`: for every $d \ge m$ and every $F$ homogeneous of degree $d$, one has $F \in J$ if and only if, for each $i$, the pullback along $\iota$ of the section of the structure sheaf on $D_+(X_i)$ given by $F/X_i^{d}$ (built from `HomogeneousLocalization.mk` via `Proj.awayToSection`) is zero in $\Gamma(Z, \iota^{-1}D_+(X_i))$. The conclusion is that for every $d \ge m$: first, for each $i : \mathbb{N}$ the group $\ker d^{i+1} / \operatorname{im} d^{i}$ of the ordered-cover Čech complex of the twist presheaf `ProjSpace.twist (ιk ≫ ProjSpace.π k n) ιk d` over the cover of $Z$ pulled back from the standard charts is a subsingleton; secondly, every cochain $c$ in the kernel of $d^0$ admits a homogeneous $F$ of degree $d$ such that for every $0$-simplex $s$ of the cover and every $i$, the $i$-th component $(c\,s).val\ i$ is the restriction to $\mathrm{inter}\,s \sqcap \iota^{-1}D_+(X_i)$ of the pullback of $F/X_i^{d}$.
--
--   This is the degenerate base case of the cohomological Gotzmann-regularity induction used in the construction of the Hilbert functor: the hypothesis on `piece J m` says that the subscheme cut out in degrees $\ge m$ is empty, so all twisted Čech groups are trivial and the representation of global sections by forms holds vacuously. It feeds the two statements [`AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth`](thm.html#AlgebraicGeometry.ProjSpace.forall_H0_twist_exists_of_forall_subsingleton_HSucc_of_maximal_growth) and [`AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth`](thm.html#AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_maximal_growth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero.lean

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

theorem AlgebraicGeometry.ProjSpace.forall_subsingleton_HSucc_twist_and_forall_H0_exists_of_finrank_piece_eq_zero
    (n m : ℕ) (k : Type) [Field k]
    (J : Ideal (MvPolynomial (Fin (n + 1)) k)) (hJ0 : Module.finrank k (piece J m) = 0)
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
