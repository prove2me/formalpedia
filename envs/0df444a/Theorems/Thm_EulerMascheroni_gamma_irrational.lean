-- Prove2me | Theorems.Thm_EulerMascheroni_gamma_irrational
-- name    : EulerMascheroni.gamma_irrational
-- status  : Open
-- author  : @shivm
-- created : 2026-09-10T06:42:33.788462+00:00
-- url     : https://prove2.me/theorems/66a4e48a-f260-4615-92d3-686ca9356509
-- title:
--   Euler's constant is irrational
-- statement:
--   Euler's constant $\gamma$ is irrational: $\gamma \notin \mathbb{Q}$.
--
--   This is **open**, and is the weaker of the two arithmetic questions about $\gamma$ — transcendence implies irrationality but not conversely. It is the older and more famous form of the problem: despite $\gamma$ having been computed to hundreds of billions of digits, and despite explicit criteria equivalent to its irrationality being available since Sondow's work, no proof is known.
--
--   What is known is conditional or disjunctive: any rational representation would need a denominator exceeding $10^{244663}$, and at least one of $\gamma$ and the Euler--Gompertz constant $\delta$ must be irrational.
--
--   **Formalization note.** `Irrational x` is Mathlib's predicate that `x` is not in the range of the coercion $\mathbb{Q} \to \mathbb{R}$.
-- source:
--   Open problem. Survey: J. Lagarias, Euler's constant: Euler's work and modern developments, Bull. Amer. Math. Soc. 50 (2013), https://arxiv.org/abs/1303.1856, Section 5 (Irrationality and transcendence).

import Definitions.Def_eulerMascheroni_gompertz

open Real

namespace EulerMascheroni
theorem gamma_irrational : Irrational Real.eulerMascheroniConstant := by sorry
end EulerMascheroni
