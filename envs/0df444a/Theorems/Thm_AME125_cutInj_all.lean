-- Prove2me | Theorems.Thm_AME125_cutInj_all
-- name    : AME125.cutInj_all
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:14:00.791589+00:00
-- url     : https://prove2.me/theorems/24bf4e1b-67d2-55dc-923c-470a9e417b6c
-- title:
--   AME125: cut Inj all
-- statement:
--   **Every set of six parties satisfies the cut condition** for the authors' graph.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L195-L211
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L195-L211

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix

theorem AME125.cutInj_all (A : Finset (Fin 12)) (hA : A.card = 6) : CutInj (U + Uᵀ) A := by sorry
