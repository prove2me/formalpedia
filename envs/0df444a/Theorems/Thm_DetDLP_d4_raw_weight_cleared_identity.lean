-- Prove2me | Theorems.Thm_DetDLP_d4_raw_weight_cleared_identity
-- name    : DetDLP.d4_raw_weight_cleared_identity
-- status  : Proved
-- author  : @Bingsheng
-- created : 2026-11-24T10:46:09.745049+00:00
-- url     : https://prove2.me/theorems/b69c173b-884c-49cc-a61b-8ba359133089
-- title:
--   Cleared guard-tree identity for raw branch weights
-- statement:
--   Consider an expansion of depth $D$ starting at depth zero and precision $p$, and let $g$ be its total guard. Every rank has raw loss at most $g$. At precision $g+p$, multiply its reduced raw coefficient and its leaf product by two to the power of its unused guard. Summing these terms over all ranks gives exactly $2^g$ times the canonical lift of the root value. The coefficients in this identity use the original branch weights, not quotient witnesses.
-- source:
--   DetDLP, Appendix D.4, cleared contraction identity for a stopped expansion.

import Definitions.Def_DetDLP_D4RawGuard
set_option autoImplicit false
open Polynomial DetDLP.AppendixD4 DetDLP.ResidualScalarOracle DetDLP.D4GuardTree DetDLP.D4GuardTree.Expansion

theorem DetDLP.d4_raw_weight_cleared_identity {S D p l : ℕ} {f : ℤ[X]} {hf : f.Monic} {z : B f l p}
    (e : Expansion S f hf l 0 D p z) :
    let g := totalGuard S D; let q := g+p
    (∀ r, rawLossSum e r ≤ g) ∧
    (∑ r : e.Ranks, (2 : B f l q) ^ (g - rawLossSum e r) * red f l q (rawCoeff e r) * e.leaves q r) =
      2 ^ g * lift hf q z := by sorry
