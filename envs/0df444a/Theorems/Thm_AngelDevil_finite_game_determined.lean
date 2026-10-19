-- Prove2me | Theorems.Thm_AngelDevil_finite_game_determined
-- name    : AngelDevil.finite_game_determined
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-18T13:36:55.36345+00:00
-- url     : https://prove2.me/theorems/755f9736-9c48-4e56-a844-ee7810ff855b
-- title:
--   Finite-horizon Angel-Devil determinacy
-- statement:
--   For every nonnegative power p and finite horizon T, either one Angel strategy is safe for T rounds against every Devil, or one Devil strategy prevents every Angel strategy from being safe for T rounds. Both strategies use the original history interfaces. At horizon zero the first alternative holds. This is the finite-horizon determinacy step used with compactness in the confinement argument.
-- source:
--   Mathe, The Angel of power 2 wins (2007), https://doi.org/10.1017/S0963548306008303, author manuscript pp. 1-2, determinacy observation and Claim 2.1 proof; finite-horizon intermediate statement.

import Definitions.Def_AngelDevil_FiniteHorizon
open AngelDevil

theorem AngelDevil.finite_game_determined (p T : Nat) :
    FiniteAngelWins p T ∨ ∃ D, ∀ A, ¬ SafeFor p A D T := by sorry
