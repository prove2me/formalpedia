-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_oesort
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.obd_oesort
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/c5b1ab0c-cefe-5618-9de6-8c89a8ef5a00
-- title:
--   Signed sorting commutes with the ordered Čech boundary
-- statement:
--   Let $V$ be a scheme and let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $K.\iota$ together with opens $U_i \subseteq V$, each affine, whose supremum is $\top$. For $n : \mathbb{N}$ write $K.\mathrm{OIdx}\,n = (\mathrm{Fin}(n+1) \to K.\iota)$ for the $(n+1)$-tuples of indices and $K.\mathrm{OCh}\,n$ for the finitely supported $\mathbb{Z}$-valued functions on this type, i.e. the free abelian group on such tuples. Two $\mathbb{Z}$-linear maps are in play, each obtained by extending a rule on generators via `K.olin`: the alternating boundary `K.obd n : K.OCh (n+1) →ₗ[ℤ] K.OCh n`, sending a generator $u$ (an $(n+2)$-tuple) to $\sum_{j : \mathrm{Fin}(n+2)} (-1)^j\,[\,u \circ \mathrm{Fin.succAbove}\,j\,]$, the $j$-th face being $u$ with its $j$-th entry deleted; and the signed sorting map `K.oesort n : K.OCh n →ₗ[ℤ] K.OCh n`, sending a generator $u$ to $\mathrm{sign}(\mathrm{Tuple.sort}\,u) \cdot [\,u \circ \mathrm{Tuple.sort}\,u\,]$ when $u$ is injective and to $0$ otherwise. The assertion is that for every $x \in K.\mathrm{OCh}(n+1)$ one has $\partial(\,\mathrm{oesort}_{n+1}(x)\,) = \mathrm{oesort}_n(\partial x)$, the boundary being `K.obd n` in both cases.
--
--   This is the statement that signed sorting is a chain map on the $\mathbb{Z}$-chains of tuples of cover indices, identifying the alternating Čech complex with its ordered (strictly increasing) subcomplex up to sign; the two ingredients are the behaviour of $\mathrm{Fin.succAbove}$ under a permutation together with the corresponding sign rule, and the compatibility of sorting with deletion of an entry. It is used in the proof of [`AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ohom_add_ohom_obd`](thm.html#AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ohom_add_ohom_obd), where the chain homotopy comparing the two complexes is verified.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_oesort.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.obd_oesort
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (n : ℕ) (x : K.OCh (n + 1)) :
    K.obd n (K.oesort (n + 1) x) = K.oesort n (K.obd n x) := by sorry
