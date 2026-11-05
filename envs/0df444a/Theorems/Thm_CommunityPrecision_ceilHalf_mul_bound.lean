-- Prove2me | Theorems.Thm_CommunityPrecision_ceilHalf_mul_bound
-- name    : CommunityPrecision.ceilHalf_mul_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-04T08:44:11.538362+00:00
-- url     : https://prove2.me/theorems/5f97dfd2-d22e-4036-9f70-555fd176c222
-- title:
--   CommunityPrecisionProfile: Ceil Half mul bound
-- statement:
--   Precision accounting for arbitrary finite profiles of Gaussian-integer operations.
--
--   [Original Lean source](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/CommunityPrecisionProfile.lean#L18-L24). Imported from CrocSwap/integer-mult-bounds at `7c49fe32c55d`. Original work by Alejandro Zarzuelo Urdiales, with the assistance and predecessor credits recorded in the source provenance. [Attribution notice](https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/NOTICE). Apache-2.0. Imported by marwahaha using lean-splitter.
-- source:
--   https://github.com/CrocSwap/integer-mult-bounds/blob/7c49fe32c55de02c2c873655c804b16e4c3fef0a/research/gaussian-parity-synthesis/CommunityPrecisionProfile.lean#L18-L24 | Apache-2.0 | CrocSwap contributors; see pinned NOTICE | lean-splitter import, independently validated on Hetzner

import Std
import Definitions.Def_CommunityPrecisionProfile
set_option autoImplicit true
open CommunityPrecision

theorem CommunityPrecision.ceilHalf_mul_bound (r f : Nat) :
    ceilHalf (r*f) ≤ ceilHalf r * f := by sorry
