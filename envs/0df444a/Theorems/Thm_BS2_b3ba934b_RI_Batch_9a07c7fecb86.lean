-- Prove2me | Theorems.Thm_BS2_b3ba934b_RI_Batch_9a07c7fecb86
-- name    : BS2_b3ba934b_RI_Batch_9a07c7fecb86
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T19:09:45.273589+00:00
-- url     : https://prove2.me/theorems/3731f557-0fa7-49fd-bfa1-ba1c507bf7cb
-- title:
--   Sensitivity record certificate: Batch_9a07c7fecb86
-- statement:
--   Conjunction of these already accepted exact record-certificate facts: checked_length0, checked_length1, checked_length2, checked_length3. Each component is reused with its original statement and attribution.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RecordSmall.lean; original SHA-256 c4589bf645b1f6149bbd8d184c850b786d160bf0d2702c12acf66b82ca5c38cc; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40RecordTreeData
import Definitions.Def_BS2_b3ba934b_RecordChunking
set_option autoImplicit false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
set_option Elab.async false
open ThreeBoundEndpoint40Records ThreeBoundRecordLookup

theorem BS2_b3ba934b_RI_Batch_9a07c7fecb86 : (ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 0=true) ∧ (ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 1=true) ∧ (ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 2=true) ∧ (ThreeBoundRecordLookup.checkLength ThreeBoundEndpoint40Records.tree 3=true) ∧ True := by sorry
