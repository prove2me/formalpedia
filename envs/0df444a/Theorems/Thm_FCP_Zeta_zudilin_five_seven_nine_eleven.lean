-- Prove2me | Theorems.Thm_FCP_Zeta_zudilin_five_seven_nine_eleven
-- name    : FCP.Zeta.zudilin_five_seven_nine_eleven
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T20:54:03.868852+00:00
-- url     : https://prove2.me/theorems/a925cba9-6bcf-4296-940d-3886687da227
-- title:
--   Zudilin: one of $\zeta(5), \zeta(7), \zeta(9), \zeta(11)$ is irrational
-- statement:
--   **Zudilin's theorem (2001).** At least one of $\zeta(5)$, $\zeta(7)$, $\zeta(9)$, $\zeta(11)$ is irrational. The proof refines the Ball--Rivoal hypergeometric construction; the theorem is the sharpest known localisation of irrationality among small odd zeta values, and it does not identify which value is irrational.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/RiemannZetaValues.lean); W. Zudilin, One of the numbers $\zeta(5), \zeta(7), \zeta(9), \zeta(11)$ is irrational, Russ. Math. Surv. 56 (2001), 774--776

import Mathlib

namespace FCP.Zeta

theorem zudilin_five_seven_nine_eleven :
    ({5, 7, 9, 11} ∩ {a : ℕ | ∃ x : ℝ, Irrational x ∧ riemannZeta a = x}).Nonempty := by sorry

end FCP.Zeta
