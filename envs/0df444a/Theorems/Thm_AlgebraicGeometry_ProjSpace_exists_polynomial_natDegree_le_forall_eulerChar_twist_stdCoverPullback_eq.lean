-- Prove2me | Theorems.Thm_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq
-- name    : AlgebraicGeometry.ProjSpace.exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:45.469968+00:00
-- url     : https://prove2.me/theorems/5b5da173-fab6-5a05-89e3-c23e5760f26a
-- title:
--   Snapper polynomiality of the Čech Euler characteristic on Pⁿ_k
-- statement:
--   Let $k$ be a field, let $n$ be a natural number, let $Z$ be a scheme, and let $\iota : Z \to \operatorname{Proj}\big(\bigoplus_m (k[X_0,\dots,X_n])_m\big)$ be a closed immersion into the Proj of the graded algebra of homogeneous components of $\mathrm{MvPolynomial}\,(\mathrm{Fin}\,(n+1))\,k$. Write $\pi$ for the structure morphism $\iota$ followed by $\mathrm{ProjSpace.\pi}\,k\,n : \operatorname{Proj} \to \operatorname{Spec} k$. For each $d \in \mathbb{N}$, `ProjSpace.twist` $\pi\,\iota\,d$ is the presheaf of $k$-modules on $Z$ assigning to an open $U$ the module of families $(g_i)_{i \in \mathrm{Fin}(n+1)}$ with $g_i \in \Gamma(Z, U \sqcap \mathrm{pullbackChart}\,\iota\,i)$ subject to the degree-$d$ compatibility predicate `TwistCompat`, with restriction maps induced by restriction of sections; `ProjSpace.stdCoverPullback` $\iota$ is the ordered affine cover of $Z$ indexed by $\mathrm{ULift}(\mathrm{Fin}(n+1))$ whose $j$-th member is $\iota^{-1}$ of the basic open locus of $X_j$ in $\operatorname{Proj}$. The assertion is that there exists a polynomial $P \in \mathbb{Q}[t]$ with $\deg P \le n$ such that for every $d \in \mathbb{N}$ the Euler characteristic $\sum_{i=0}^{n} (-1)^i \dim_k \check H^i$ of that twist presheaf on this cover, viewed in $\mathbb{Q}$, equals $P(d)$.
--
--   This is Snapper's polynomiality theorem for the Euler characteristic of $\mathcal{O}_Z(d) = \iota^{*}\mathcal{O}(d)$ on a closed subscheme $Z \subseteq \mathbb{P}^n_k$, in the Čech formulation on the pulled-back standard affine cover. It feeds the Hilbert-polynomial bookkeeping used downstream, in particular the statement computing $\dim_k \check H^0$ of the twist when the higher Čech groups vanish.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_ProjSpace_exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_ProjSpace
import Definitions.Def_AlgebraicGeometry_ProjSpaceCover
import Definitions.Def_AlgebraicGeometry_ProjTwistDatum
import Definitions.Def_AlgebraicGeometry_OModulePresheafEulerChar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MvPolynomial TensorProduct

attribute [local instance] MvPolynomial.gradedAlgebra

theorem AlgebraicGeometry.ProjSpace.exists_polynomial_natDegree_le_forall_eulerChar_twist_stdCoverPullback_eq
    {k : Type u} [Field k] {n : ℕ} {Z : Scheme.{u}}
    (ι : Z ⟶ Proj (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k)) [IsClosedImmersion ι] :
    ∃ P : Polynomial ℚ, P.natDegree ≤ n ∧
      ∀ d : ℕ,
        ((ProjSpace.twist (ι ≫ ProjSpace.π k n) ι d).eulerChar (ProjSpace.stdCoverPullback ι) : ℚ) = P.eval (d : ℚ) := by sorry
