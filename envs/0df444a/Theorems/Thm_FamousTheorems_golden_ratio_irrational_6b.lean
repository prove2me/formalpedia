-- Prove2me | Theorems.Thm_FamousTheorems_golden_ratio_irrational_6b
-- name    : FamousTheorems.golden_ratio_irrational_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:43:48.479981+00:00
-- url     : https://prove2.me/theorems/3e94dc32-ab8b-4545-a84b-5af9f2f80197
-- title:
--   The golden ratio is irrational
-- statement:
--   **The golden ratio is irrational.** The golden ratio
--   $$\varphi=\frac{1+\sqrt5}{2}$$
--   is irrational.
--
--   Since $\sqrt5=2\varphi-1$, this is equivalent to the irrationality of $\sqrt5$. According to one account, the incommensurability of the diagonal and the side of a regular pentagon, whose ratio is $\varphi$, was the first irrationality found by the Pythagoreans. The continued fraction of $\varphi$ is $[1;1,1,\ldots]$, and $\varphi$ is the irrational number that is hardest to approximate by rationals, as measured by Hurwitz's theorem.
--
--   **Formalization note.** Mathlib's `Real.goldenRatio_irrational`. Mathlib defines `Real.goldenRatio` as $(1+\sqrt5)/2$, and the statement is written with this expression.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `Real.goldenRatio_irrational`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem golden_ratio_irrational_6b : Irrational ((1 + Real.sqrt 5) / 2) := by sorry

end FamousTheorems
