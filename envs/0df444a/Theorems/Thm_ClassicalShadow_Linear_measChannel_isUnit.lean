-- Prove2me | Theorems.Thm_ClassicalShadow_Linear_measChannel_isUnit
-- name    : ClassicalShadow.Linear.measChannel_isUnit
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-18T20:11:45.674984+00:00
-- url     : https://prove2.me/theorems/7e1ba230-2c78-4135-9a3a-3f1d680b5539
-- title:
--   p. 11, after (S2) — tomographic completeness makes the measurement channel M invertible
-- statement:
--   Let $\mathcal U = \{(w_i, U_i)\}$ be a finite measurement primitive on $n$ qubits and let
--   $$\mathcal M(X) = \sum_i w_i \sum_{b \in \{0,1\}^n} \langle b|U_i X U_i^\dagger|b\rangle\, U_i^\dagger|b\rangle\langle b|U_i$$
--   be its measurement channel, viewed as a linear map on $2^n \times 2^n$ complex matrices. If $\mathcal U$ is tomographically complete, then $\mathcal M$ is invertible:
--   $$\mathcal M \ \text{is a unit of } \operatorname{End}_{\mathbb C}\big(\mathbb C^{2^n\times 2^n}\big).$$
--
--   This is what makes the classical shadow $\hat\rho = \mathcal M^{-1}(U^\dagger|\hat b\rangle\langle\hat b|U)$ well defined.
--
--   **Formalization Note.** Invertibility is stated as `IsUnit` in the endomorphism ring, so that `Ring.inverse` of the channel, used as $\mathcal M^{-1}$ throughout, is the true two-sided inverse.
-- source:
--   Huang, Kueng, Preskill, Predicting many properties of a quantum system from very few measurements, arXiv:2002.08953v2, p. 11, paragraph after (S2)

import Mathlib
import Definitions.Def_ClassicalShadow_Linear_Setting

namespace ClassicalShadow.Linear
theorem measChannel_isUnit {n : ℕ} {ι : Type} [Fintype ι] (E : Primitive n ι)
    (hE : TomographicallyComplete E) : IsUnit (measChannel E) := by sorry
end ClassicalShadow.Linear
