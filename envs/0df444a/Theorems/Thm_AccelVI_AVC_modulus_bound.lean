-- Prove2me | Theorems.Thm_AccelVI_AVC_modulus_bound
-- name    : AccelVI.AVC.modulus_bound
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T09:03:08.566963+00:00
-- url     : https://prove2.me/theorems/0974ba19-ff00-4aea-baa2-595f0827b740
-- title:
--   Proof of Lemma 5.3, p. 9 — for μ ∈ [−1, 1], ½|μ + 1 ± √(μ² − 1)| ≤ 1, the + case being ½√2·√(1 + μ)
-- statement:
--   Let $\mu\in[-1,1]$, so that $\mu^2-1\le0$ and $\sqrt{\mu^2-1}=i\sqrt{1-\mu^2}$. Then
--   $$\tfrac12\big|\mu+1+\sqrt{\mu^2-1}\big|=\tfrac12\sqrt{(\mu+1)^2+\big(\sqrt{1-\mu^2}\big)^2}=\tfrac12\sqrt2\cdot\sqrt{1+\mu}\le1,$$
--   and likewise
--   $$\tfrac12\big|\mu+1-\sqrt{\mu^2-1}\big|\le1.$$
--
--   With (5.4)–(5.5), this bounds the modulus of both roots of (5.3) by $1-\sqrt{1/\kappa}$ whenever $\mu$ is a real eigenvalue of $L_\pi$ in $[-1,1]$.
--
--   **Formalization Note.** The complex square root $\sqrt{\mu^2-1}$ of the page is written explicitly as $i\sqrt{1-\mu^2}$ (with the real square root of the nonnegative number $1-\mu^2$), which is its value for $\mu\in[-1,1]$; $|\cdot|$ is the complex modulus.
-- source:
--   Goyal & Grand-Clément, A First-Order Approach to Accelerated Value Iteration, arXiv:1905.09963v7, p. 9, proof of Lemma 5.3, display after 'Now for µ ∈ [−1, 1]' and the following sentence

import Mathlib
import Definitions.Def_mm_basic
import Definitions.Def_AccelVI_AVC_Setting

namespace AccelVI.AVC

/-- Proof of Lemma 5.3, p. 9: for `μ ∈ [−1, 1]`, where `√(μ² − 1) = i√(1 − μ²)`,
`½|μ + 1 + √(μ² − 1)| = ½√((μ + 1)² + (√(1 − μ²))²) = ½√2 · √(1 + μ) ≤ 1`, and
`½|μ + 1 − √(μ² − 1)| ≤ 1`. -/
theorem modulus_bound (μ : ℝ) (hμ : μ ∈ Set.Icc (-1 : ℝ) 1) :
    1 / 2 * ‖(μ : ℂ) + 1 + Complex.I * (Real.sqrt (1 - μ ^ 2) : ℂ)‖ =
        1 / 2 * Real.sqrt ((μ + 1) ^ 2 + (Real.sqrt (1 - μ ^ 2)) ^ 2) ∧
    1 / 2 * Real.sqrt ((μ + 1) ^ 2 + (Real.sqrt (1 - μ ^ 2)) ^ 2) =
        1 / 2 * Real.sqrt 2 * Real.sqrt (1 + μ) ∧
    1 / 2 * Real.sqrt 2 * Real.sqrt (1 + μ) ≤ 1 ∧
    1 / 2 * ‖(μ : ℂ) + 1 - Complex.I * (Real.sqrt (1 - μ ^ 2) : ℂ)‖ ≤ 1 := by sorry

end AccelVI.AVC
