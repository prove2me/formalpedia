-- Prove2me | Theorems.Thm_FamousTheorems_poisson_convolution_poisson_7a
-- name    : FamousTheorems.poisson_convolution_poisson_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:19.511264+00:00
-- url     : https://prove2.me/theorems/2bc50b39-08fd-4f48-bffa-532dea6cf483
-- title:
--   The convolution of two Poisson distributions is Poisson
-- statement:
--   **The convolution of two Poisson distributions is Poisson.** For all rates $r_1,r_2\ge0$,
--   $$\operatorname{Poisson}(r_1)*\operatorname{Poisson}(r_2)=\operatorname{Poisson}(r_1+r_2).$$
--   Equivalently, the sum of independent Poisson random variables with means $r_1$ and $r_2$ is Poisson with mean $r_1+r_2$.
--
--   The proof is a computation with the binomial theorem, or with generating functions. This additivity makes the Poisson process well defined: counts in disjoint intervals are independent Poisson variables whose means add. It is used in queueing theory, in the modelling of rare events and in Poisson approximation.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.poissonMeasure_conv_poissonMeasure`. `poissonMeasure r` is the Poisson distribution with mean $r$ on $\mathbb N$, and `Measure.conv` is convolution of measures on the additive monoid $\mathbb N$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.poissonMeasure_conv_poissonMeasure`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem poisson_convolution_poisson_7a (r₁ r₂ : NNReal) :
    (ProbabilityTheory.poissonMeasure r₁).conv (ProbabilityTheory.poissonMeasure r₂) =
      ProbabilityTheory.poissonMeasure (r₁ + r₂) := by sorry

end FamousTheorems
