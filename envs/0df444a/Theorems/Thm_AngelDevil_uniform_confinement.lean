-- Prove2me | Theorems.Thm_AngelDevil_uniform_confinement
-- name    : AngelDevil.uniform_confinement
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:16:21.861571+00:00
-- url     : https://prove2.me/theorems/2202ef8d-e4d0-4b0b-81af-3c0549e73536
-- title:
--   Claim 2.1 and determinacy: a uniform confinement box
-- statement:
--   For each positive integer power, if no single Angel strategy survives against every Devil, there is a positive integer radius and one Devil strategy such that every safe finite play remains inside that box. The radius and Devil are chosen before the Angel strategy and play length. This target includes the introductory determinacy observation as well as Claim 2.1; neither is assumed as an extra hypothesis.
-- source:
--   Andras Mathe, The Angel of power 2 wins, CPC 16 (2007), 363-374; https://doi.org/10.1017/S0963548306008303; author manuscript internal pagination. Claim 2.1, p. 2, and the introductory determinacy observation, p. 1.

import Definitions.Def_AngelDevil_Game
open AngelDevil

theorem AngelDevil.uniform_confinement (p : Nat) (hp : 0 < p)
    (h : ¬ AngelWins p) : ∃ N, 0 < N ∧ ∃ D : DevilStrategy,
    ∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n)) := by sorry
