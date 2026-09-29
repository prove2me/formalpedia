-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ohom_add_ohom_obd
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ohom_add_ohom_obd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/f95abc42-dbce-5647-936b-da337f6128d7
-- title:
--   Cone homotopy between identity and sorting on ordered Čech chains
-- statement:
--   Let $V$ be a scheme and let $K$ be an ordered affine cover of $V$, i.e. a finite linearly ordered index type $K.\iota$ together with opens $U_i \subseteq V$, each affine, whose supremum is $\top$. Let $n$ be a natural number and let $\sigma \in K.\mathrm{OIdx}(n+1)$, that is, an arbitrary map $\sigma : \mathrm{Fin}(n+2) \to K.\iota$ (repetitions allowed, no monotonicity required). The assertion is an identity in the group `K.OCh (n+1)` of finitely supported $\mathbb{Z}$-valued functions on $K.\mathrm{OIdx}(n+1)$: $$\mathrm{obd}_{n+1}\bigl(\mathrm{ohom}_{n+1}(\sigma)\bigr) + \mathrm{olin}_n(\mathrm{ohom}_n)\bigl(\mathrm{obd}_n(\delta_\sigma)\bigr) = \delta_\sigma - \mathrm{oesort}_{n+1}(\delta_\sigma),$$ where $\delta_\sigma$ is the basis element `Finsupp.single σ 1`; `obd n` is the $\mathbb{Z}$-linear map sending a basis tuple $u$ to $\sum_{j} (-1)^j \delta_{u \circ \mathrm{succAbove}\, j}$ (alternating sum of the faces obtained by deleting the $j$-th entry); `olin n f` is the $\mathbb{Z}$-linear extension of a function $f$ on tuples; `oesort n` sends a basis tuple $u$ to $\mathrm{sign}(\mathrm{sort}\,u)\,\delta_{u \circ \mathrm{sort}\, u}$ when $u$ is injective and to $0$ otherwise; and `ohom` is defined by recursion, $\mathrm{ohom}_0 = 0$ and $\mathrm{ohom}_{n+1}(\sigma) = \mathrm{ocone}_{\sigma(0)}\bigl(\delta_\sigma - \mathrm{oesort}_{n+1}(\delta_\sigma) - \mathrm{olin}_n(\mathrm{ohom}_n)(\mathrm{obd}_n(\delta_\sigma))\bigr)$, with $\mathrm{ocone}_m$ the linear map prepending the index $m$ to a tuple. The geometric data of the cover enter only through the linearly ordered index type; the identity itself is combinatorial.
--
--   This is the homotopy identity making `ohom` a chain homotopy, in the ordered Čech chain complex of the cover, between the identity and the signed sorting operator `oesort`; in degree $n$ it says that the difference between a tuple and its ordered representative is a boundary up to the homotopy term. It is used in the comparison between ordered and unordered Čech cochains, through [`AlgebraicGeometry.OModulePresheaf.sub_oext_ores_mem_of_od_eq_zero`](thm.html#AlgebraicGeometry.OModulePresheaf.sub_oext_ores_mem_of_od_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ohom_add_ohom_obd.lean

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

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ohom_add_ohom_obd
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (n : ℕ) (σ : K.OIdx (n + 1)) :
    K.obd (n + 1) (K.ohom (n + 1) σ) + K.olin n (K.ohom n) (K.obd n (Finsupp.single σ 1)) =
      Finsupp.single σ 1 - K.oesort (n + 1) (Finsupp.single σ 1) := by sorry
