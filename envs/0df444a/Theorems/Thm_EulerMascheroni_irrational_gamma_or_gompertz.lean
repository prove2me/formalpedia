-- Prove2me | Theorems.Thm_EulerMascheroni_irrational_gamma_or_gompertz
-- name    : EulerMascheroni.irrational_gamma_or_gompertz
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-10T06:58:02.07978+00:00
-- url     : https://prove2.me/theorems/d222b292-2598-49e0-b8ab-da47afe474cb
-- title:
--   At least one of $\gamma$ and $\delta$ is irrational (Aptekarev)
-- statement:
--   At least one of Euler's constant $\gamma$ and the Euler--Gompertz constant $\delta$ is irrational:
--
--   $$\gamma \notin \mathbb{Q} \quad\text{or}\quad \delta \notin \mathbb{Q}.$$
--
--   Unlike the mission's goal, this is a **theorem**, not a conjecture. It is the strongest unconditional irrationality statement known about $\gamma$. Aptekarev was the first to record it, on the basis of earlier work of Mahler and Shidlovskii which implied it without stating it: simultaneous Pade approximation to the pair of functions underlying $\gamma$ and $\delta$ forces a linear independence that cannot hold if both constants are rational.
--
--   The disjunction is the essential limitation. The approximations control $\gamma$ and $\delta$ jointly and do not separate them, so the argument yields no information about either constant on its own. Formalizing it is a substantive target: it needs the Pade/Hermite construction and its determinant non-vanishing, not merely the statement.
-- source:
--   A. I. Aptekarev, On linear forms containing the Euler constant, https://arxiv.org/abs/0902.1768 (2009); building on K. Mahler, Applications of a theorem by A. B. Shidlovski, Proc. Roy. Soc. London Ser. A 305 (1968), 149-173. Summarized in J. Lagarias, Bull. AMS 50 (2013), https://arxiv.org/abs/1303.1856, Section 5.

import Definitions.Def_eulerMascheroni_gompertz

open Real

namespace EulerMascheroni
theorem irrational_gamma_or_gompertz :
    Irrational Real.eulerMascheroniConstant ∨ Irrational gompertzConstant := by sorry
end EulerMascheroni
