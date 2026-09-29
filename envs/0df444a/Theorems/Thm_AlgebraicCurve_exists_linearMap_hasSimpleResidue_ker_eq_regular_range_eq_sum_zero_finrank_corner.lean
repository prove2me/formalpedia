-- Prove2me | Theorems.Thm_AlgebraicCurve_exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner
-- name    : AlgebraicCurve.exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.809948+00:00
-- url     : https://prove2.me/theorems/1ae5e63f-31ac-55fd-8daf-031dc2eb882a
-- title:
--   Residue map on differentials with simple poles along S
-- statement:
--   Let $K$ be an algebraically closed field and $F$ a field extension of $K$ that is essentially of finite type over $K$, such that $F$ is a curve over $K$ in the sense of [`AlgebraicCurve.IsCurveOver`](def/AlgebraicCurve_IsCurveOver.html#L15) (every nonzero $f \in F$ has a divisor of degree $0$ whose value at each place $v$ is $v.\mathrm{ord}(f)$, each residue field of a place is a finite-dimensional $K$-space, and $\Omega[F/K]$ is free of rank $1$ over $F$) and such that every nonzero $\omega \in \Omega[F/K]$ has a divisor whose value at $v$ is $v.\mathrm{ordDifferential}(\omega)$. Here a place is a valuation subring of $F$ containing $K$, distinct from $F$ and a principal ideal ring. Let $S$ be a finite set of places, and let $M = \mathrm{polarDifferentials}\,K\,F\,S$ be the $K$-subspace of $\omega \in \Omega[F/K]$ with $\omega = f \cdot dt_v$ for some $f$ in the valuation ring of $v$ when $v \notin S$, and $\omega = f \cdot dt_v$ with $t_v f$ in the valuation ring of $v$ when $v \in S$, where $t_v$ is the chosen uniformizer at $v$ and $dt_v$ its differential. The assertion is that there exists a $K$-linear map $\mathrm{res} \colon M \to (\text{places} \to K)$ such that: for every $\omega \in M$ and $v \in S$, $\mathrm{res}(\omega)(v)$ is a simple residue of $\omega$ at $v$, i.e. $\omega = f \cdot dt_v$ for some $f$ with $t_v f$ in the valuation ring of $v$ and with residue the image of $\mathrm{res}(\omega)(v)$ in the residue field; $\mathrm{res}(\omega)(v) = 0$ for $v \notin S$; $\mathrm{res}(\omega) = 0$ if and only if $\omega$ lies in $\mathrm{regularDifferentials}\,K\,F$ (that is, $\omega = f \cdot dt_v$ with $f$ in the valuation ring, at every place); the range of $\mathrm{res}$ consists exactly of the functions $r$ vanishing off $S$ with $\sum_{v \in S} r(v) = 0$; $M$ is a finite-dimensional $K$-space; and, finally, for every $K$-linear $E \colon M \to M$ with $E \circ E = E$ and every $K$-linear $\bar e$ on the space of functions on places with $\mathrm{res} \circ E = \bar e \circ \mathrm{res}$, one has $\dim_K \mathrm{range}(E) = \dim_K E(\ker \mathrm{res}) + \dim_K \bar e(\mathrm{range}\,\mathrm{res})$; no idempotency is assumed of $\bar e$.
--
--   This packages the classical residue exact sequence $0 \to H^0(X,\Omega^1) \to H^0(X,\Omega^1(S)) \to (K^S)_{\Sigma = 0} \to 0$ for a complete curve over an algebraically closed field, together with the resulting dimension count on the image of an idempotent $E$ that is compatible with $\mathrm{res}$ via an operator $\bar e$ on residue vectors. It is used in the modular-curve computations of ranks of corners cut out by Hecke idempotents on differentials with at most simple poles along the supersingular places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_CanonicalDivisor
import Definitions.Def_AlgebraicCurve_PolarDifferentials

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AlgebraicCurve

theorem AlgebraicCurve.exists_linearMap_hasSimpleResidue_ker_eq_regular_range_eq_sum_zero_finrank_corner
    {K F : Type*} [Field K] [Field F] [Algebra K F] [IsAlgClosed K] [Algebra.EssFiniteType K F]
    [AlgebraicCurve.IsCurveOver K F] [AlgebraicCurve.HasCanonicalDivisor (K := K) (F := F)]
    (S : Finset (AlgebraicCurve.Place K F)) :
    ∃ res : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) →ₗ[K]
        (AlgebraicCurve.Place K F → K),

      (∀ (ω : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))))
          (v : AlgebraicCurve.Place K F), v ∈ S → v.HasSimpleResidue (ω : Ω[F⁄K]) (res ω v)) ∧
      (∀ (ω : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))))
          (v : AlgebraicCurve.Place K F), v ∉ S → res ω v = 0) ∧

      (∀ ω : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))),
          res ω = 0 ↔ (ω : Ω[F⁄K]) ∈ AlgebraicCurve.regularDifferentials K F) ∧

      (∀ r : AlgebraicCurve.Place K F → K,
          r ∈ LinearMap.range res ↔ (∀ v : AlgebraicCurve.Place K F, v ∉ S → r v = 0) ∧ ∑ v ∈ S, r v = 0) ∧

      Module.Finite K ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) ∧

      (∀ (E : ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))) →ₗ[K]
            ↥(AlgebraicCurve.polarDifferentials K F (S : Set (AlgebraicCurve.Place K F))))
          (ē : (AlgebraicCurve.Place K F → K) →ₗ[K] (AlgebraicCurve.Place K F → K)),
          E ∘ₗ E = E → res ∘ₗ E = ē ∘ₗ res →
          Module.finrank K ↥(LinearMap.range E) =
            Module.finrank K ↥((LinearMap.ker res).map E) + Module.finrank K ↥((LinearMap.range res).map ē)) := by sorry
