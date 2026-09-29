-- Prove2me | Theorems.Thm_EulerMascheroni_gamma_irrational_of_transcendental
-- name    : EulerMascheroni.gamma_irrational_of_transcendental
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-10T06:44:55.487904+00:00
-- url     : https://prove2.me/theorems/d777a7c5-9d53-42b6-8ce7-86612a31cdb2
-- title:
--   Transcendence of $\gamma$ implies its irrationality
-- statement:
--   If Euler's constant is transcendental then it is irrational.
--
--   This is the implication linking the mission's two targets, and it holds for any real number: a rational number $q$ is a root of $X - q \in \mathbb{Q}[X]$, hence algebraic, so a transcendental real cannot be rational. It is recorded as its own node so that the dependency between the transcendence goal and the irrationality target is explicit in the mission graph rather than implicit.
--
--   **Formalization note.** Mathlib supplies this as `Transcendental.irrational`, so the content here is the specialization to `Real.eulerMascheroniConstant`, not a new argument. Note the implication runs only in this direction: irrationality of $\gamma$ would not settle transcendence.
-- source:
--   Elementary; the general statement is Mathlib's `Transcendental.irrational`.

import Definitions.Def_eulerMascheroni_gompertz

open Real

namespace EulerMascheroni
theorem gamma_irrational_of_transcendental
    (h : Transcendental ℚ Real.eulerMascheroniConstant) :
    Irrational Real.eulerMascheroniConstant := by sorry
end EulerMascheroni
