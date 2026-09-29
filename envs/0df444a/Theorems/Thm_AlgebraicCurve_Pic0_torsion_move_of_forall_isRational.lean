-- Prove2me | Theorems.Thm_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational
-- name    : AlgebraicCurve.Pic0.torsion.move_of_forall_isRational
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:38.65155+00:00
-- url     : https://prove2.me/theorems/6c7117c8-af54-5787-a983-e4cad2624846
-- title:
--   Moving torsion classes off a finite set, with rational support
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume the project's class `HasPrincipalDivisors K F`, i.e. that for every nonzero $f \in F$ there is a finitely supported integer-valued function $D$ on the places of $F/K$ with $D(v) = \mathrm{ord}_v(f)$ for all $v$ and $\deg D = 0$; here a place is a valuation subring of $F$ containing $\mathrm{algebraMap}\,K\,F$'s image, distinct from $F$ itself, and a principal ideal ring, a divisor is an element of `Place K F →₀ ℤ`, the degree is the sum of the coefficients weighted by the residue degrees $\deg v$, `Divisor.degZero` is the kernel of the degree map, and $\mathrm{Pic}^0$ is `Divisor.degZero` modulo the subgroup of principal divisors lying in it. Assume further that every place $v$ of $F/K$ is rational in the sense of the project's `Place.IsRational`, i.e. the map $K \to$ (residue field of $v$) is surjective. Then for every natural number $n$, every element $x$ of the $n$-torsion subgroup `Pic0.torsion K F n` (the $\mathbb{Z}$-torsion of $\mathrm{Pic}^0(K,F)$ by $n$) and every finite set $S$ of places, there is a degree-zero divisor $D$ whose class is $x$, all of whose support points are rational, and none of whose support points lies in $S$.
--
--   This is the moving lemma for divisor classes in the form used later: a torsion class can be represented by a degree-zero divisor supported away from a prescribed finite set of places and at rational points only. It is invoked in the construction of the divisorial Weil pairing data, where representing divisors with disjoint rational supports are needed, by [`AlgebraicCurve.Pic0.exists_weilPairing`](thm.html#AlgebraicCurve.Pic0.exists_weilPairing), [`AlgebraicCurve.Pic0.exists_antisymmWeilPairing`](thm.html#AlgebraicCurve.Pic0.exists_antisymmWeilPairing) and [`AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData`](thm.html#AlgebraicCurve.Pic0.nonempty_divisorialWeilPairingData).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_Pic0_torsion_move_of_forall_isRational.lean

import Definitions.Def_AlgebraicCurve_PlaceEvaluation

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicCurve

theorem AlgebraicCurve.Pic0.torsion.move_of_forall_isRational {K F : Type*} [Field K] [Field F] [Algebra K F] [HasPrincipalDivisors K F] (hrat : ∀ v : Place K F, v.IsRational) (n : ℕ) (x : Pic0.torsion K F n) (S : Finset (Place K F)) :
    ∃ D : Divisor.degZero (K := K) (F := F),
      Pic0.mk D = (x : Pic0 K F) ∧
      (∀ v ∈ (D : Divisor K F).support, Place.IsRational v) ∧
      (∀ v ∈ (D : Divisor K F).support, v ∉ S) := by sorry
