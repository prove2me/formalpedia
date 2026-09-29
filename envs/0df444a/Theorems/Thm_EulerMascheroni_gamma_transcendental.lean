-- Prove2me | Theorems.Thm_EulerMascheroni_gamma_transcendental
-- name    : EulerMascheroni.gamma_transcendental
-- status  : Open
-- author  : @shivm
-- created : 2026-09-10T06:41:55.351039+00:00
-- url     : https://prove2.me/theorems/1f5d0eac-7c79-43aa-b5f9-0cd302f56ad9
-- title:
--   Euler's constant is transcendental
-- statement:
--   Euler's constant
--
--   $$\gamma \;=\; \lim_{n\to\infty}\left(\sum_{k=1}^{n}\frac{1}{k} - \log n\right)$$
--
--   is transcendental: it is not a root of any non-zero polynomial with rational coefficients.
--
--   This is the goal of the mission and is **open**. It is expected to be true — no classical constant of this kind is believed to be algebraic — but nothing close to a proof is known, and even the far weaker assertion that $\gamma$ is irrational is open. The transcendence methods that settled $e$ (Hermite, 1873) and $\pi$ (Lindemann, 1882) do not apply, because $\gamma$ is not known to be a period or a value of the exponential at an algebraic point.
--
--   **Formalization note.** `Transcendental ℚ x` is Mathlib's predicate that `x` is not algebraic over $\mathbb{Q}$, and `Real.eulerMascheroniConstant` is Mathlib's definition of $\gamma$ as the limit of $\sum_{k \le n} 1/k - \log n$.
-- source:
--   Open problem. Background: J. Havil, Gamma: Exploring Euler's Constant, Princeton, 2003; R. P. Brent and P. Zimmermann, Modern Computer Arithmetic, and the survey J. Lagarias, Euler's constant: Euler's work and modern developments, Bull. Amer. Math. Soc. 50 (2013), https://arxiv.org/abs/1303.1856, Section 1.

import Definitions.Def_eulerMascheroni_gompertz

open Real

namespace EulerMascheroni
theorem gamma_transcendental : Transcendental ℚ Real.eulerMascheroniConstant := by sorry
end EulerMascheroni
