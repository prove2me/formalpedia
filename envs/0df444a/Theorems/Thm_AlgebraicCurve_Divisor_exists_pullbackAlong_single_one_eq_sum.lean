-- Prove2me | Theorems.Thm_AlgebraicCurve_Divisor_exists_pullbackAlong_single_one_eq_sum
-- name    : AlgebraicCurve.Divisor.exists_pullbackAlong_single_one_eq_sum
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.21649+00:00
-- url     : https://prove2.me/theorems/c7d0c2b8-3318-5dc8-9418-18a8d314310f
-- title:
--   Pull-back of a degree-one place as a sum of n places
-- statement:
--   Let $K$, $F$, $F'$ be fields with $F$ and $F'$ $K$-algebras, and assume $F'$ satisfies `HasPrincipalDivisors` over $K$, i.e. every nonzero $f \in F'$ has a divisor whose coefficient at each place is the order of $f$ there and whose degree is $0$. Here a place of $F/K$ is a valuation subring of $F$ containing $\operatorname{im}(K \to F)$, distinct from $F$ itself and a principal ideal ring, its degree being the $K$-dimension of its residue field, and a divisor is a finitely supported $\mathbb{Z}$-valued function on places. Let $\varphi : F \to F'$ be a $K$-algebra map whose underlying ring map is integral; via the $F$-algebra structure on $F'$ induced by $\varphi$, assume the fundamental identity `FundamentalIdentityAlong`: for every place $v$ of $F$, $\sum_{w \mid v} e(w/v)\deg w = [F':F]\deg v$. Let $P$ be a place of $F$ with $\deg P = 1$, assume every place $w$ of $F'$ whose restriction along $\varphi$ (the comap of its valuation subring) equals $P$ has $\deg w = 1$, and let $n$ be a natural number with $[F':F] = n$ for that algebra structure. Then there is a family $W : \mathrm{Fin}\,n \to$ places of $F'$ such that the pull-back along $\varphi$ of the divisor $1 \cdot P$ equals $\sum_{i} 1 \cdot W_i$, and every $W_i$ restricts along $\varphi$ to $P$.
--
--   This is the fundamental equality for an integral extension of function fields, in the special case of a rational place all of whose points above it are rational: the pull-back divisor $\varphi^{*}(P)$ is the fibre of $P$ enumerated with multiplicity by an $n$-element index set, each $w \mid P$ occurring $e(w/P)$ times. It is used in the study of Hecke correspondences on $X_1(p)$, where divisors of the form $\varphi^{*}(P)$ must be written as explicit sums of single places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Divisor_exists_pullbackAlong_single_one_eq_sum.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_Correspondence

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem AlgebraicCurve.Divisor.exists_pullbackAlong_single_one_eq_sum
    {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F']
    [AlgebraicCurve.HasPrincipalDivisors K F']
    (φ : F →ₐ[K] F') (hφ : φ.toRingHom.IsIntegral) (hFI : AlgebraicCurve.FundamentalIdentityAlong K φ hφ)
    (P : AlgebraicCurve.Place K F) (hdegP : P.deg = 1)
    (hdeg1 : ∀ w : AlgebraicCurve.Place K F', w.restrictAlong φ hφ = P → w.deg = 1)
    (n : ℕ) (hn : AlgebraicCurve.finrankAlong K φ = n) :
    ∃ W : Fin n → AlgebraicCurve.Place K F',
      AlgebraicCurve.Divisor.pullbackAlong φ hφ (Finsupp.single P 1) = ∑ i, Finsupp.single (W i) 1 ∧
        ∀ i, (W i).restrictAlong φ hφ = P := by sorry
