-- Prove2me | Theorems.Thm_DetDLP_w3_fp_polywire_assemble
-- name    : DetDLP.w3_fp_polywire_assemble
-- status  : Open
-- author  : @Bingsheng
-- created : 2026-11-24T23:22:06.165943+00:00
-- url     : https://prove2.me/theorems/d03fe60f-9911-4a2d-bece-60280bba71b8
-- title:
--   DetDLP WireKit: Assemble fp polyWireFamily from M3A
-- statement:
--   Given modMul, the proved M3A CoreFamily, and PolyT certificates for fpBuild and fpEntry, assemble w3_polyWireFamily for all fp queries.
-- source:
--   DetDLP manuscript, WireKit / M3A–M3B bridge (private mission), Lean workspace prove2me_workspace

import Definitions.Def_DetDLP_W3_WireCore
import Definitions.Def_DetDLP_W3_ModMul
import Definitions.Def_DetDLP_M3A_FpWireCore
import Definitions.Def_DetDLP_M3A_FpPolyDefs

set_option autoImplicit false

open DetDLP DetDLP.M3A

/-- Package the proved native fp core family with `fpBuild`/`fpEntry` PolyT certificates
    into a `w3_polyWireFamily` for all fp queries (avoids HashFull). -/

theorem DetDLP.w3_fp_polywire_assemble (mul : w3_modMulInterface)
    (hcore : FpWireCore.CoreFamily)
    (hbuild : Groundwork.PolyT FpPolyDefs.fpBuild)
    (hentry : Groundwork.PolyT FpPolyDefs.fpEntry) :
    w3_polyWireFamily w3_fpQueries := by sorry
