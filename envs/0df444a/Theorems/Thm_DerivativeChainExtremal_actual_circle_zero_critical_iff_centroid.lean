-- Prove2me | Theorems.Thm_DerivativeChainExtremal_actual_circle_zero_critical_iff_centroid
-- name    : DerivativeChainExtremal.actual_circle_zero_critical_iff_centroid
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-28T04:51:50.990179+00:00
-- url     : https://prove2.me/theorems/6528052b-2ee3-48ac-82c2-7981c33f60ec
-- title:
--   Critical circle center is exactly the source centroid
-- statement:
--   Let $p$ be a positive-degree complex polynomial all of whose roots, with multiplicity, have modulus one. The origin is a critical point of $p$ if and only if the uniform centroid of its source-root slots is zero. Repeated roots and arbitrary nonzero leading coefficient are allowed.
-- source:
--   Private repository Amal-David/derivative-chain-prize; frozen circle-centroid-v1/ExtremalCircleCentroid.lean, SHA-256 2ea7777987323954f074bb945c2ac8ab65f4a0a26d128b092e841c496f709f29; analytic checkpoint fde5728a069c8d5ad1bf06094368fcdfaefa5af7.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CenteredSource
set_option autoImplicit false
open Polynomial DerivativeChainContinuation

theorem DerivativeChainExtremal.actual_circle_zero_critical_iff_centroid (p : Polynomial ℂ)
    (hp : 0 < p.natDegree) (hunit : ∀ z∈p.roots, ‖z‖=1) :
    p.derivative.eval 0=0 ↔ rootCentroid p=0 := by sorry
