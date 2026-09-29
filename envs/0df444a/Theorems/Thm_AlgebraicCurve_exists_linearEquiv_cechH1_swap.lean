-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_linearEquiv_cechH1_swap
-- name    : AlgebraicCurve.exists_linearEquiv_cechH1_swap
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/a83585d5-1433-5b39-b2c0-0fbd5fd26bce
-- title:
--   Symmetry of the two-chart Čech H¹ in its charts
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, let $S$ and $S'$ be arbitrary sets of places of $F$ over $K$ (a place being a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring), and let $D$ be a divisor, i.e. a finitely supported function from places to $\mathbb{Z}$. For a set $T$ of places write $L_T(D)$ for the $K$-submodule [`AlgebraicCurve.lSpaceOn`](def/AlgebraicCurve_CechSectionsOfDivisor.html#L14) of $F$ consisting of those $f$ with $v(f) \le \exp(D(v))$ in $\mathbb{Z}^{m0}$ for every $v \in T$, where $v$ denotes the adic valuation attached to the place, and let $\check{H}^1((T_0,T_1),D)$ be the quotient of $L_{T_0 \cap T_1}(D)$ by the range of the Čech differential $(f_0,f_1) \mapsto f_1 - f_0$ on $L_{T_0}(D) \times L_{T_1}(D)$. The assertion is that there exists a $K$-linear equivalence $e$ from $\check{H}^1((S,S'),D)$ to $\check{H}^1((S',S),D)$ which is the identity on representatives in the strongest sense: for every $f \in F$ and every pair of witnesses $h$ for $f \in L_{S \cap S'}(D)$ and $h'$ for $f \in L_{S' \cap S}(D)$, $e$ sends the class of $\langle f, h\rangle$ to the class of $\langle f, h'\rangle$.
--
--   This records the standard fact that two-chart Čech cohomology does not depend on the ordering of the two charts, in the concrete form used for the $L$-spaces $L_T(D)$ of a divisor on a curve. The explicit identity-on-representatives clause lets later results about the Serre pairing attached to a two-chart affine open cover interchange the roles of the two charts without transporting membership proofs.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_linearEquiv_cechH1_swap.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_CechSectionsOfDivisor

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
universe u v

theorem AlgebraicCurve.exists_linearEquiv_cechH1_swap
    {K : Type u} {F : Type v} [Field K] [Field F] [Algebra K F]
    (S S' : Set (AlgebraicCurve.Place K F)) (D : AlgebraicCurve.Divisor K F) :
    ∃ e : AlgebraicCurve.cechH1 S S' D ≃ₗ[K] AlgebraicCurve.cechH1 S' S D,
      ∀ (f : F) (h : f ∈ AlgebraicCurve.lSpaceOn (S ∩ S') D) (h' : f ∈ AlgebraicCurve.lSpaceOn (S' ∩ S) D),
        e (Submodule.Quotient.mk ⟨f, h⟩) = Submodule.Quotient.mk ⟨f, h'⟩ := by sorry
