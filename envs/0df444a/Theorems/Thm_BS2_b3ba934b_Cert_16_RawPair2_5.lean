-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair2_5
-- name    : BS2_b3ba934b_Cert_16_RawPair2_5
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:01.018884+00:00
-- url     : https://prove2.me/theorems/986db645-baf9-4f6c-bebc-8e23bf76e0da
-- title:
--   Sensitivity separation: Endpoint16RawPair2_5 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair2_5. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair2_5.lean; original SHA-256 f104317e1dae19c8da4624fa6965dc695a95471137a9900294e9fa90e253843d; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair2_5 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 2 2) (recipe 2 3)).eval profile2≤661465889144801567244956340000000000000000000000000000000000000000000000 := by sorry
