-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ocone_add_ocone_obd
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ocone_add_ocone_obd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/3f351ceb-7b22-5275-8d4f-840d59a60716
-- title:
--   Cone on a vertex is a chain contraction in positive degrees
-- statement:
--   Let $V$ be a scheme and let $K$ be an ordered affine cover of $V$, that is: a finite linearly ordered index type $K.\iota$ together with opens $K.U\,i$ of $V$, each affine, whose supremum is $\top$. Fix an index $m : K.\iota$, a natural number $n$, and a chain $x \in K.\mathrm{OCh}(n+1)$, where $K.\mathrm{OCh}(k)$ denotes the free $\mathbb Z$-module of finitely supported functions on $K.\mathrm{OIdx}(k) = (\mathrm{Fin}(k+1) \to K.\iota)$, i.e. on arbitrary $(k+1)$-tuples of indices (no monotonicity is imposed). Here $K.\mathrm{obd}\,k : K.\mathrm{OCh}(k+1) \to K.\mathrm{OCh}(k)$ is the $\mathbb Z$-linear map sending the basis element at a tuple $u$ to $\sum_{j : \mathrm{Fin}(k+2)} (-1)^j\,[\,u \circ \mathrm{Fin.succAbove}\,j\,]$, the alternating sum over the faces obtained by deleting the $j$-th entry, and $K.\mathrm{ocone}\,m\,k : K.\mathrm{OCh}(k) \to K.\mathrm{OCh}(k+1)$ is the $\mathbb Z$-linear map sending the basis element at $u$ to the basis element at $\mathrm{Fin.cons}\,m\,u$, the tuple $u$ with $m$ prepended. The assertion is the homotopy identity $$K.\mathrm{obd}(n+1)\bigl(K.\mathrm{ocone}\,m\,(n+1)\,x\bigr) + K.\mathrm{ocone}\,m\,n\bigl(K.\mathrm{obd}\,n\,x\bigr) = x,$$ valid for all chains $x$ in degrees $n+1 \ge 1$.
--
--   This is the contractibility of the ordered chain complex on the index set of the cover: prepending the fixed vertex $m$ is a chain homotopy between the identity and zero in positive degrees, so every chain of tuples of length $\ge 2$ is a boundary. It is used to build the corresponding homotopy on Čech cochains, being cited by [`AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ohom_add_ohom_obd`](thm.html#AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ohom_add_ohom_obd).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_obd_ocone_add_ocone_obd.lean

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

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.obd_ocone_add_ocone_obd
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (m : K.ι) (n : ℕ) (x : K.OCh (n + 1)) :
    K.obd (n + 1) (K.ocone m (n + 1) x) + K.ocone m n (K.obd n x) = x := by sorry
