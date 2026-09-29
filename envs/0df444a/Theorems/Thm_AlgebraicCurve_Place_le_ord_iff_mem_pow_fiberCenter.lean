-- Prove2me | Theorems.Thm_AlgebraicCurve_Place_le_ord_iff_mem_pow_fiberCenter
-- name    : AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.834276+00:00
-- url     : https://prove2.me/theorems/e6dcb2e2-b711-545d-83a8-cdadb9fcaa7d
-- title:
--   Order at w versus powers of the fibre prime
-- statement:
--   Let $K \subseteq F \subseteq F'$ be fields with compatible $K$-algebra structures (so that $F'$ is an $F$-algebra and the tower is scalar-compatible), and assume $F'/F$ is finite and separable. Let $v$ be a place of $F$ over $K$, i.e. a valuation subring of $F$ containing the image of $K$, different from $F$ itself and a principal ideal ring, and let $w$ be such a place of $F'$ over $K$ whose restriction to $F$ — the preimage of its valuation subring under $F \to F'$ — equals $v$. Write $C_v$ for the integral closure of the valuation ring of $v$ in $F'$ (a Dedekind domain with fraction field $F'$, module-finite over the valuation ring of $v$) and $P_w \subset C_v$ for the height-one prime `Place.fiberCenter F' v hw`, the centre of $w$ in $C_v$. The assertion is that for every nonzero $c \in C_v$ and every $n \in \mathbb{N}$, the inequality $n \le \operatorname{ord}_w(c)$, where $\operatorname{ord}_w$ is minus the logarithm of the adic valuation attached to $w$ evaluated at the image of $c$ in $F'$, holds if and only if $c \in P_w^{\,n}$.
--
--   This is the membership form of the identity $\operatorname{ord}_w = v_{P_w}$ in the dictionary between places of $F'$ above $v$ and the height-one primes of the integral closure of the valuation ring of $v$ in $F'$. It is used to compute multiplicities of $P_w$ in principal ideals, hence in [`AlgebraicCurve.Place.count_normalizedFactors_span_singleton`](thm.html#AlgebraicCurve.Place.count_normalizedFactors_span_singleton), and in the construction of elements of prescribed order in [`AlgebraicCurve.Place.exists_isIntegral_adjoin_eq_top_ord_sub_algebraMap_eq_one`](thm.html#AlgebraicCurve.Place.exists_isIntegral_adjoin_eq_top_ord_sub_algebraMap_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Place_le_ord_iff_mem_pow_fiberCenter.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_PlacesOverDVR

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Place.le_ord_iff_mem_pow_fiberCenter {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [FiniteDimensional F F'] [Algebra.IsSeparable F F'] {v : Place K F} {w : Place K F'} (hw : w.restrict F = v) {c : Place.integralClosureAt F' v} (hc : c ≠ 0) (n : ℕ) : (n : ℤ) ≤ w.ord (algebraMap (Place.integralClosureAt F' v) F' c) ↔ c ∈ (Place.fiberCenter F' v hw).asIdeal ^ n := by sorry
