-- Prove2me | Theorems.Thm_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
-- name    : AlgebraicGeometry.exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:49.552687+00:00
-- url     : https://prove2.me/theorems/ce6fdfee-4ec9-5d27-b84a-d7feb41d070d
-- title:
--   Affine opens through finite sets descend to open subschemes
-- statement:
--   Let $X$ be a scheme, and suppose $X$ has the property that for every finite set $G$ of points of $X$ there is an open subset $W \subseteq X$ which is affine (i.e. satisfies `IsAffineOpen`) and contains every point of $G$. Let $U$ and $O$ be open subsets of $X$, let $F$ be a finite set of points of the open subscheme $U$, and assume that for every $x \in F$ the image $\iota_U(x)$ of $x$ under the open immersion $\iota_U \colon U \to X$ lies in $O$. Then there exists an open subset $W$ of the scheme $U$ such that $W$ is affine, $W$ is contained in the preimage $\iota_U^{-1}(O)$, and every $x \in F$ lies in $W$. Thus the hypothesis on finite sets of points of $X$ yields, for the open subscheme $U$, affine opens containing a prescribed finite set and contained in a prescribed open neighbourhood of that set.
--
--   This transports the property that finite sets of points lie in an affine open subscheme from a scheme to its open subschemes, in the relative form required as a covering hypothesis by existence theorems for schemes of relative effective divisors and relative Picard schemes. It is applied to smooth loci of two-chart integral models of curves and of models of the modular curves $X_1(N)$, with $O$ typically the preimage of an affine open of the base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry

theorem AlgebraicGeometry.exists_isAffineOpen_opens_le_preimage_forall_mem_of_forall_finset
    {X : Scheme.{u}}
    (hAF : ∀ G : Finset X, ∃ W : X.Opens, IsAffineOpen W ∧ ∀ x ∈ G, x ∈ W)
    (U O : X.Opens) (F : Finset ↥U) (hFO : ∀ x ∈ F, U.ι.base x ∈ O) :
    ∃ W : (U : Scheme.{u}).Opens, IsAffineOpen W ∧ W ≤ U.ι ⁻¹ᵁ O ∧ ∀ x ∈ F, x ∈ W := by sorry
