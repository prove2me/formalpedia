-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_16_RawPair1_2
-- name    : BS2_b3ba934b_Cert_16_RawPair1_2
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T20:29:24.954715+00:00
-- url     : https://prove2.me/theorems/45c1d0a0-a639-490f-b229-cceb1aad99ae
-- title:
--   Sensitivity separation: Endpoint16RawPair1_2 raw_pair_bound checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint16RawPair1_2. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint16RawPair1_2.lean; original SHA-256 620b07289131ae6c2b4a3ae4c840a0ae3a083a9ae0295ce03053cda21bd9cbf5; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint16NumericData
import Definitions.Def_BS2_b3ba934b_Endpoint16RawData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundMinmaxNumeric ThreeBoundMinmaxNumeric.Endpoint16

theorem BS2_b3ba934b_Cert_16_RawPair1_2 : (ThreeBoundMinmaxA.rawAExpr 16 caps records
    (recipe 1 2) (recipe 1 2)).eval profile1≤192825632236769287372743000000000000000000000000000000000000000000000000 := by sorry
