-- Prove2me | Theorems.Thm_Comp_dirac_ne_zero_iff
-- name    : Comp.dirac_ne_zero_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T23:47:21.493299+00:00
-- url     : https://prove2.me/theorems/7571945c-bf74-4fc3-8430-32ae286b486e
-- title:
--   Comp: dirac ne zero iff
-- statement:
--   A point mass is nonzero exactly at its own point -- the support fact the qualitative operators
--       actually consume.
--
--   Source: https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L95-L99
-- source:
--   https://github.com/gabrielhrs/markovgames/blob/1814771f360f11f8486c30bee81106dcf0b1a524/Comp/SafetyChainQ.lean#L95-L99

import Definitions.Def_Comp_Objective
import Definitions.Def_Comp_QualitativeFinset
import Definitions.Def_Comp_SafetyChainQ
set_option autoImplicit true
set_option linter.hashCommand false
open Comp
open Csg

theorem Comp.dirac_ne_zero_iff (t s' : Chain) : dirac t s' ≠ 0 ↔ s' = t := by sorry
