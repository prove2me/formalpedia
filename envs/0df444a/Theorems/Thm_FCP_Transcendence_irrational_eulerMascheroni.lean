-- Prove2me | Theorems.Thm_FCP_Transcendence_irrational_eulerMascheroni
-- name    : FCP.Transcendence.irrational_eulerMascheroni
-- status  : Open
-- author  : @Lucas
-- created : 2026-09-15T20:55:00.775572+00:00
-- url     : https://prove2.me/theorems/57e3e0da-db89-4296-8def-4e776ed5ec51
-- title:
--   Irrationality of the Euler--Mascheroni constant $\gamma$
-- statement:
--   **Is $\gamma$ irrational?** The Euler--Mascheroni constant $\gamma = \lim_{n\to\infty}\left(\sum_{k\le n} 1/k - \log n\right) \approx 0.5772$ is not known to be irrational; the statement is recorded here in the affirmative. Known partial results are of the form 'at least one of $\gamma$ and a companion constant is transcendental' (Rivoal, 2012).
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Irrational.lean); https://en.wikipedia.org/wiki/Euler%27s_constant

import Mathlib

namespace FCP.Transcendence

theorem irrational_eulerMascheroni : Irrational Real.eulerMascheroniConstant := by sorry

end FCP.Transcendence
