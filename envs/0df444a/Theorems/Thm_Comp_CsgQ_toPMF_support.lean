-- Prove2me | Theorems.Thm_Comp_CsgQ_toPMF_support
-- name    : Comp.CsgQ.toPMF_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T22:53:08.13568+00:00
-- url     : https://prove2.me/theorems/996eed3c-8b2d-43f3-9e96-1decae7e3f5b
-- title:
--   Csg Q: to PMF support
-- statement:
--   **The bridge.** The cast game's `PMF` support is exactly the rational support. This is the only
--       place the qualitative line touches `PMF` at all, and everything above it works with `supportQ`.
--
--       `ENNReal.ofReal x = 0 ↔ x ≤ 0`, so nonzero mass means a strictly positive rational weight, which
--       given `WellFormed`'s nonnegativity is the same as a nonzero one.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Qualitative.lean#L81-L96
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/Qualitative.lean#L81-L96

import Definitions.Def_Comp_Basic
import Definitions.Def_Csg_QualitativeSure
import Definitions.Def_Comp_Lattice
import Definitions.Def_Comp_Qualitative
set_option autoImplicit true
open Comp
open Csg
open Comp.CsgQ
variable {S A1 A2 : Type*} [Fintype S] [Fintype A1] [Fintype A2] [Nonempty A1] [Nonempty A2]
  [DecidableEq A1] [DecidableEq A2]

theorem Comp.CsgQ.toPMF_support (G : CsgQ S A1 A2) (h : G.WellFormed) (s : S) (a1 : A1) (a2 : A2) :
    (G.toPMF h s a1 a2).support = G.supportQ s a1 a2 := by sorry
