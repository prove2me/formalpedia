-- Prove2me | Theorems.Thm_EulerMascheroni_transcendental_gamma_or_gompertz
-- name    : EulerMascheroni.transcendental_gamma_or_gompertz
-- status  : Open
-- author  : @shivm
-- created : 2026-09-10T06:58:27.193984+00:00
-- url     : https://prove2.me/theorems/080e0ab4-6c5a-4a58-99f4-00c8aa7ff5be
-- title:
--   At least one of $\gamma$ and $\delta$ is transcendental (Rivoal)
-- statement:
--   At least one of Euler's constant $\gamma$ and the Euler--Gompertz constant $\delta$ is transcendental.
--
--   This is Rivoal's strengthening of the disjunctive irrationality statement, and it is again a **theorem** rather than a conjecture. It upgrades the conclusion from "not both rational" to "not both algebraic", by running the Pade-approximation argument against arbitrary algebraic numbers rather than only rationals.
--
--   As with the irrationality version, the disjunction cannot presently be resolved in either direction; deciding which of the two constants it refers to would settle a problem open since Euler. Together with the irrationality disjunction it marks the boundary of what Diophantine approximation currently reaches for these constants.
-- source:
--   T. Rivoal, On the arithmetic nature of the values of the gamma function, Euler's constant, and Gompertz's constant, Michigan Math. J. 61 (2012), 239-254. Summarized in J. Lagarias, Bull. AMS 50 (2013), https://arxiv.org/abs/1303.1856, Section 5.

import Definitions.Def_eulerMascheroni_gompertz

open Real

namespace EulerMascheroni
theorem transcendental_gamma_or_gompertz :
    Transcendental ℚ Real.eulerMascheroniConstant ∨ Transcendental ℚ gompertzConstant := by sorry
end EulerMascheroni
