-- Prove2me | Theorems.Thm_BrooksTheorem_brooks
-- name    : BrooksTheorem.brooks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:34:28.062094+00:00
-- url     : https://prove2.me/theorems/98d28f52-9423-59ca-966f-851e6db4e425
-- title:
--   Brooks Theorem: brooks
-- statement:
--   **Brooks' theorem (1941).** A finite connected graph that is neither complete nor an odd
--   cycle can be coloured with as many colours as its maximum degree.
--
--   Source: https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Brooks.lean#L45-L68
-- source:
--   https://github.com/jtraverso/brooks/blob/b99e6f500256586626396de9c2d6fd4d96119d60/BrooksLib/Brooks.lean#L45-L68

module
public import Mathlib
public import Definitions.Def_BrooksLib_BrooksLow
public import Definitions.Def_BrooksLib_Brooks
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open BrooksTheorem
variable {V : Type*}

theorem BrooksTheorem.brooks [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] (hconn : G.Connected)
    (hK : G ≠ ⊤) (hC : ∀ n, Odd n → IsEmpty (G ≃g cycleGraph n)) :
    G.Colorable G.maxDegree := by sorry
