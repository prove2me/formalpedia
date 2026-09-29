-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_obd
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.obd_obd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/e3528687-c2bf-532c-9ebe-bbc5bf775117
-- title:
--   Ordered Čech boundary squares to zero
-- statement:
--   Let $V$ be a scheme and let $K$ be an ordered affine cover of $V$, i.e. the data of an index type $K.\iota$ that is finite and linearly ordered, a family of opens $K.U : K.\iota \to V.\mathrm{Opens}$, a proof that each $K.U\,i$ is an affine open, and a proof that $\bigsqcup_i K.U\,i = \top$. For each $n$ the index set $K.\mathrm{OIdx}\,n$ is the type $\mathrm{Fin}(n+1) \to K.\iota$ of $(n+1)$-tuples of indices, and the group of ordered $n$-chains $K.\mathrm{OCh}\,n$ is the group of finitely supported functions $K.\mathrm{OIdx}\,n \to \mathbb{Z}$, i.e. the free abelian group on those tuples. The boundary $K.\mathrm{obd}\,n : K.\mathrm{OCh}(n+1) \to_{\mathbb Z} K.\mathrm{OCh}\,n$ is the unique $\mathbb{Z}$-linear map sending a generator $u : K.\mathrm{OIdx}(n+1)$ to $\sum_{j : \mathrm{Fin}(n+2)} (-1)^{j}\,\delta_{K.\mathrm{oface}\,u\,j}$, where $K.\mathrm{oface}\,u\,j = u \circ \mathrm{Fin.succAbove}\,j$ is the tuple obtained by deleting the $j$-th entry of $u$. The assertion is that for every natural number $n$ and every chain $x \in K.\mathrm{OCh}(n+2)$ one has $K.\mathrm{obd}\,n\,(K.\mathrm{obd}(n+1)\,x) = 0$; thus the maps $K.\mathrm{obd}$ form a complex. The conclusion involves $K$ only through its index type, and is purely combinatorial.
--
--   This is the standard identity $\partial \circ \partial = 0$ for the (ordered) Čech chain complex attached to a finite ordered affine cover, which is what makes the ordered Čech construction a complex. It is used in [`AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ohom_add_ohom_obd`](thm.html#AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ohom_add_ohom_obd), where the chain homotopy identity for the comparison maps between covers requires the vanishing of a double boundary.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_obd.lean

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

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.obd_obd
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (n : ℕ) (x : K.OCh (n + 2)) :
    K.obd n (K.obd (n + 1) x) = 0 := by sorry
