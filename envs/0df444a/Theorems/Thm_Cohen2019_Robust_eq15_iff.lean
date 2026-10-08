-- Prove2me | Theorems.Thm_Cohen2019_Robust_eq15_iff
-- name    : Cohen2019.Robust.eq15_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T09:33:11.077126+00:00
-- url     : https://prove2.me/theorems/727ef38b-184f-4606-93b4-3ac840d67d27
-- title:
--   Eq. (15) — $\Phi(\Phi^{-1}(\overline{p_B}) + r/\sigma) < \Phi(\Phi^{-1}(\underline{p_A}) - r/\sigma)$ iff $r < \frac{\sigma}{2}(\Phi^{-1}(\underline{p_A}) - \Phi^{-1}(\overline{p_B}))$
-- statement:
--   Let $\sigma > 0$ and $0 < \underline{p_A}, \overline{p_B} < 1$, and let $\Phi$ be the standard Gaussian CDF. For every real $r$,
--   $$
--   \Phi\Big(\Phi^{-1}(\overline{p_B}) + \frac{r}{\sigma}\Big) < \Phi\Big(\Phi^{-1}(\underline{p_A}) - \frac{r}{\sigma}\Big)
--   \iff
--   r < \frac{\sigma}{2}\Big(\Phi^{-1}(\underline{p_A}) - \Phi^{-1}(\overline{p_B})\Big). \qquad (15)
--   $$
--
--   With $r = \|\delta\|$ the two sides of the left inequality are $\mathbb P(Y \in B)$ and $\mathbb P(Y \in A)$ by (13) and (14), so this is the step "$\mathbb P(Y \in A) > \mathbb P(Y \in B)$ if and only if $\|\delta\| < R$" that recovers the certified radius.
--
--   **Formalization Note** $\Phi^{-1}$ is the real inverse of $\Phi$ on $(0,1)$; the statement is the algebraic step of the paper with a real number $r$ in place of $\|\delta\|$.
-- source:
--   Cohen, Rosenfeld, Kolter, Certified Adversarial Robustness via Randomized Smoothing, arXiv:1902.02918v2, proof of Theorem 1, eq. (15), p. 14 (PDF page)

import Mathlib
import Definitions.Def_Cohen2019_Robust_Phi

namespace Cohen2019.Robust

open MeasureTheory ProbabilityTheory

/-- **Eq. (15).** Cohen, Rosenfeld, Kolter, *Certified Adversarial Robustness via Randomized
Smoothing*, arXiv:1902.02918v2, proof of Theorem 1, eq. (15), p. 14 (PDF page): "algebra shows that
`ℙ(Y ∈ A) > ℙ(Y ∈ B)` if and only if `‖δ‖ < (σ/2)(Φ⁻¹(p̲A) − Φ⁻¹(p̄B))`", where by (13) and (14)
`ℙ(Y ∈ A) = Φ(Φ⁻¹(p̲A) − ‖δ‖/σ)` and `ℙ(Y ∈ B) = Φ(Φ⁻¹(p̄B) + ‖δ‖/σ)`.

**Formalization Note.** This is the algebraic step, stated for the right-hand sides of (13), (14)
with `r` in place of `‖δ‖` (any real `r`). `Φ⁻¹` is the real inverse `PhiInvReal` on `(0, 1)`;
`0 < p̲A, p̄B < 1` is the regime in which (13), (14) are stated. -/
theorem eq15_iff (σ : ℝ) (hσ : 0 < σ) (pA pB : ℝ) (hpA0 : 0 < pA) (hpA1 : pA < 1)
    (hpB0 : 0 < pB) (hpB1 : pB < 1) (r : ℝ) :
    Phi (PhiInvReal pB + r / σ) < Phi (PhiInvReal pA - r / σ)
      ↔ r < σ / 2 * (PhiInvReal pA - PhiInvReal pB) := by sorry

end Cohen2019.Robust
