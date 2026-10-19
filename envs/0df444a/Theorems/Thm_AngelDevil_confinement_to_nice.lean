-- Prove2me | Theorems.Thm_AngelDevil_confinement_to_nice
-- name    : AngelDevil.confinement_to_nice
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:16:23.740249+00:00
-- url     : https://prove2.me/theorems/573ba228-d8a4-41f7-ab55-9aad2fd7f68d
-- title:
--   Theorem 2.4: transfer confinement to a Nice Devil
-- statement:
--   Let p and N be nonnegative integers. If a Devil strategy keeps every safe finite play of the power-p Angel inside the box of radius N, then some Nice Devil does the same. The assumption ranges over every Angel strategy and every finite time, requiring safety only up to that time. This formalization includes the degenerate cases p = 0 and N = 0 in addition to the positive parameters in the paper.
-- source:
--   Andras Mathe, The Angel of power 2 wins, CPC 16 (2007), 363-374; https://doi.org/10.1017/S0963548306008303; author manuscript internal pagination. Theorem 2.4, pp. 2-3, with harmless zero-parameter extension.

import Definitions.Def_AngelDevil_NiceReduction
open AngelDevil

theorem AngelDevil.confinement_to_nice (p N : Nat) (D : DevilStrategy)
    (hc : ∀ A n, (∀ m, m < n →
      Jump p (current (play A D m)) (current (play A D (m+1))) ∧
      some (current (play A D (m+1))) ∉ (play A D (m+1)).burned) →
      InBox N (current (play A D n))) : NiceCanConfine p N  := by sorry
