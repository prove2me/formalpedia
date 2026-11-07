-- Prove2me | Theorems.Thm_AGProxGap_lemma_3_2
-- name    : AGProxGap.lemma_3_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:37:29.851409+00:00
-- url     : https://prove2.me/theorems/6caf1a56-10d8-4b1d-8081-82cee6e5adc3
-- title:
--   Lemma 3.2 — at most $2\mathfrak g-2-\deg A$ points $P$ with $l(A+P)>0$
-- statement:
--   Let $X$ be a smooth projective irreducible curve of genus $\mathfrak g$ over an algebraically closed field $k$, and let $A$ be a divisor on $X$ with
--   $$
--   l(A)=0\qquad\text{and}\qquad \deg A\le \mathfrak g-2 .
--   $$
--   Then only finitely many points $P\in X(k)$ satisfy $l(A+P)>0$, and their number is at most
--   $$
--   2\mathfrak g-2-\deg A .
--   $$
--   Here $l(B)=\dim_k L(B)$. The lemma drives the inductive choice of the auxiliary points in Lemma 3.3: at each step only finitely many points are forbidden.
--
--   **Formalization Note** The curve is its function field $F/k$ (`IsCurveOver`, `EssFiniteType`, `ConstantsAreBase`); points are all places of $F/k$, each of degree one since $k$ is algebraically closed. $l$ is `ell`, the genus is `genusFF k F`, and the count is `Set.ncard` together with a separate finiteness clause.
--
--   Differences from the source:
--   - encoding: a smooth projective irreducible curve X/k, points of X(k) → a field F with IsCurveOver k F, Algebra.EssFiniteType k F, ConstantsAreBase k F; all places of F/k; genus genusFF k F; reason: over an algebraically closed field these are exactly the function fields of such curves, and every place is a k-point
-- source:
--   Li, Xing, Yuan, Zhu, On Proximity Gaps for One-Point Algebraic Geometric Codes, arXiv:2610.39256 (held version, sha256 d2017986…3b3f), Lemma 3.2, p.17

import Mathlib
import Definitions.Def_AlgebraicCurve_AdelicIndex
import Definitions.Def_AlgebraicCurve_PlaceEvaluation
import Definitions.Def_AlgebraicCurve_IsCurveOver

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve
open Classical

universe u v

namespace AGProxGap

/-- **Lemma 3.2** (Li, Xing, Yuan, Zhu, *On Proximity Gaps for One-Point Algebraic Geometric Codes*, arXiv:2610.39256 (held version, sha256 d2017986…), §3, p.17): "Let X be a smooth projective irreducible curve of genus 𝔤 over
an algebraically closed field k. Let A be a divisor on X satisfying l(A) = 0 and deg(A) ≤ 𝔤 − 2.
Then there are only finitely many points P ∈ X(k) such that l(A+P) > 0. More precisely, the
number of such points is at most 2𝔤 − 2 − deg(A)."

**Formalization Note** The curve is its function field `F/k` (`IsCurveOver k F`,
`Algebra.EssFiniteType k F`, `ConstantsAreBase k F`, `k` algebraically closed). Points of `X(k)`
are all places of `F/k` (each has degree one over an algebraically closed field).
`l(A) = AlgebraicCurve.ell A = dim_k L(A)`, `deg = Divisor.degree`, and `𝔤 = genusFF k F`
(`dim_k A/(A(0) + F)`, the genus since `L(0) = k`). Both clauses are stated: finiteness, and the
bound on the number of points (`Set.ncard`, cast to `ℤ`). -/
theorem lemma_3_2 {k : Type*} [Field k] [IsAlgClosed k] {F : Type*} [Field F] [Algebra k F]
    [IsCurveOver k F] [Algebra.EssFiniteType k F] (hF : ConstantsAreBase k F)
    (A : Divisor k F) (hA : ell A = 0) (hdeg : Divisor.degree A ≤ (genusFF k F : ℤ) - 2) :
    {Q : Place k F | 0 < ell (A + Finsupp.single Q (1 : ℤ))}.Finite ∧
      ({Q : Place k F | 0 < ell (A + Finsupp.single Q (1 : ℤ))}.ncard : ℤ) ≤
        2 * (genusFF k F : ℤ) - 2 - Divisor.degree A := by sorry

end AGProxGap
