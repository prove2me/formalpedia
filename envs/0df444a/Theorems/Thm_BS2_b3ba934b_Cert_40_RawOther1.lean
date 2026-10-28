-- Prove2me | Theorems.Thm_BS2_b3ba934b_Cert_40_RawOther1
-- name    : BS2_b3ba934b_Cert_40_RawOther1
-- status  : Proved
-- author  : @yousofy
-- created : 2026-10-27T04:59:19.723343+00:00
-- url     : https://prove2.me/theorems/ce137140-44b7-4030-a555-a752204e0b2c
-- title:
--   Sensitivity separation: Endpoint40RawOther1 ordinary_and_transfer checkpoint
-- statement:
--   The exact finite numeric assertion from Endpoint40RawOther1. The interface exposes the statement independently of the original certificate proof source; its complete proof must be verified before any dependent goal is submitted.
-- source:
--   Attached verified checkpoint block_sensitivity_three_bounds; lean_project/Endpoint40RawOther1.lean; original SHA-256 15710e6c55ee11e4a046b5b89fe298fcb02fbaa6201d2071ad28fe7e0bd697eb; campaign https://prove2.me/campaigns/block-sensitivity-vs-sensitivity

import Definitions.Def_BS2_b3ba934b_Endpoint40NumericData
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 2000000
set_option maxHeartbeats 0
open ThreeBoundNumeric ThreeBoundFullProfile
open ThreeBoundNumeric.Endpoint40

theorem BS2_b3ba934b_Cert_40_RawOther1 :
    (∀ i j : Fin 40, i≤j →
    ((recipe 1 j).tolerance=0 ∨ 3≤(recipe 1 j).tolerance) →
    (rawAExpr 40 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j)) ∧
    (∀ (ha : ∀ i j : Fin 40, i≤j →
      (rawAExpr 40 caps records (recipe 1 i) (recipe 1 j)).eval profile1≤rawProfile1 (.a i j)),
∀ coord : Coord 40, valid coord → raw 1 profile1 coord≤rawProfile1 coord) := by sorry
