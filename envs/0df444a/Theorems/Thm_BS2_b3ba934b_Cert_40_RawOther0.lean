-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther0
-- name    : BS2_b3ba934b_Cert_40_RawOther0
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T01:11:07.809512+00:00
-- url     : https://prove2.me/theorems/ec61bf57-cb94-4af1-a3fb-51c8495c839f
-- title:
--   Sensitivity separation: Endpoint40RawOther0 ordinary_and_transfer checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawOther0. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther0.lean; original SHA-256 d53272d11f47d3bc685ee8a7a6f661d9f2352a5e749d43135fd15aa3fa6a4d93; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawOther0 :
    (∀ i j : Fin 40, i≤j →
    ((recipe 0 j).tolerance=0 ∨ 3≤(recipe 0 j).tolerance) →
    (rawAExpr 40 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 0 i) (recipe 0 j)).eval profile0≤rawProfile0 (.a i j)),
∀ coord : Coord 40, valid coord → raw 0 profile0 coord≤rawProfile0 coord) := by sorry
