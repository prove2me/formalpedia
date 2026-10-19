-- Prove2me | Theorems.Thm_AngelDevil_nice_devil_reduction
-- name    : AngelDevil.nice_devil_reduction
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T12:47:22.151585+00:00
-- url     : https://prove2.me/theorems/76719177-828c-4447-b573-06ec5a9f0684
-- title:
--   Theorem 2.7: reduction to a Nice Devil
-- statement:
--   For every positive integer power, if the Angel has no winning strategy, some Nice Devil can keep every finite safe play in a fixed box of positive integer radius. This formulation includes the determinacy observation from the introduction in addition to Theorem 2.7.
-- source:
--   Andras Mathe, The Angel of power 2 wins, CPC 16 (2007), 363-374; https://doi.org/10.1017/S0963548306008303; author manuscript internal pagination. Theorem 2.7, manuscript p. 3, with the introductory determinacy observation on p. 1.

import Definitions.Def_AngelDevil_Game

theorem AngelDevil.nice_devil_reduction (p : Nat) (hp : 0 < p) : ¬ AngelDevil.AngelWins p → ∃ N, 0 < N ∧ AngelDevil.NiceCanConfine p N := by sorry
