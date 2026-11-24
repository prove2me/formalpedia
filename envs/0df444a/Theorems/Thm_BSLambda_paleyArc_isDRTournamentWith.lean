-- Prove2me | Theorems.Thm_BSLambda_paleyArc_isDRTournamentWith
-- name    : BSLambda.paleyArc_isDRTournamentWith
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T00:52:47.725269+00:00
-- url     : https://prove2.me/theorems/f8e4586e-6cdd-4ecc-8f2b-49561404650f
-- title:
--   BSLambda: paley Arc is DRTournament With
-- statement:
--   **The Paley tournament is doubly regular.**  If `F_k` has odd characteristic and `-1` is a
--   nonresidue in it — equivalently, `k ≡ 3 mod 4` — then the Paley orientation of `F_k` is a
--   doubly regular tournament with out-degree `d = (k - 1) / 2` and `t = (k - 3) / 4` common
--   neighbours. (Section 2 of `bs_lambda.txt`.)
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L236-L268
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/BlockSpectralSensitivity/Paley/Tournament.lean#L236-L268

module
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Defs_Tournament
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic
public import Mathlib.Tactic.NormNum.Prime
public import Definitions.Def_LeanPool_BlockSpectralSensitivity_Paley_Tournament
set_option autoImplicit true
@[expose] public section
public section
open Finset
open BSLambda

theorem BSLambda.paleyArc_isDRTournamentWith {k d t : ℕ} [Fact (Nat.Prime k)]
    (hchar : ringChar (ZMod k) ≠ 2) (hneg : quadraticChar (ZMod k) (-1) = -1)
    (hd : 2 * d + 1 = k) (ht : 4 * t + 3 = k) : IsDRTournamentWith (paleyArc k) d t := by sorry
