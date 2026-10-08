-- Prove2me | Theorems.Thm_FCP_Transcendence_irrational_catalanConstant
-- name    : FCP.Transcendence.irrational_catalanConstant
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-15T20:55:40.749887+00:00
-- url     : https://prove2.me/theorems/b4eb2968-6f82-4e40-829e-b93139bf1bae
-- title:
--   Irrationality of Catalan's constant $G$
-- statement:
--   **Is Catalan's constant irrational?** $G = \sum_{n \ge 0} (-1)^n/(2n+1)^2 \approx 0.915965$ is not known to be irrational; the statement is recorded here in the affirmative. It is the 'even' analogue of $\zeta(3)$ for the Dirichlet beta function, and the Apéry-type machinery that settles $\zeta(3)$ has so far not settled $G$.
-- source:
--   Formal Conjectures library (Google DeepMind), Apache-2.0, https://github.com/google-deepmind/formal-conjectures (FormalConjectures/Wikipedia/Irrational.lean); https://en.wikipedia.org/wiki/Catalan%27s_constant

import Mathlib
import Definitions.Def_FCP_CatalanConstant

namespace FCP.Transcendence

theorem irrational_catalanConstant : Irrational FCP.Constants.catalanConstant := by sorry

end FCP.Transcendence
