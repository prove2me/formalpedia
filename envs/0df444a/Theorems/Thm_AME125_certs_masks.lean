-- Prove2me | Theorems.Thm_AME125_certs_masks
-- name    : AME125.certs_masks
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T23:13:11.684863+00:00
-- url     : https://prove2.me/theorems/6b291daf-21f8-5e1c-972d-b573ec201d48
-- title:
--   AME125: certs masks
-- statement:
--   **The kernel check**: the masks in `certs` are exactly the 924 sets of six parties, in
--   increasing order.
--
--   Source: https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L113-L114
-- source:
--   https://github.com/zblore/fc-ame-12-5/blob/e8c1e58c7e4dd324868b6ed6a4ce59b103e2797f/AME125/Certificate.lean#L113-L114

module
public import Definitions.Def_AME125_Data
public import Definitions.Def_AME125_GraphState
public import Definitions.Def_AME125_Certificate
set_option autoImplicit false
@[expose] public section
public section
open AME125
open scoped Matrix

theorem AME125.certs_masks : certs.map Prod.fst = (List.range 4096).filter fun m ↦ popcount m = 6 := by sorry
