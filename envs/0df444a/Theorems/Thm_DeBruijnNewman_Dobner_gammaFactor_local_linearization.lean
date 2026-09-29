-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_gammaFactor_local_linearization
-- name    : DeBruijnNewman.Dobner.gammaFactor_local_linearization
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-25T00:03:03.953547+00:00
-- url     : https://prove2.me/theorems/8d968a4c-29b9-4f25-b08b-497651774718
-- title:
--   Uniform local linearization error for the Riemann gamma factor
-- statement:
--   Fix real numbers $a<b$. There exist constants $C>0$ and $Y\geq1$ such that the following holds for every $s,z\in\mathbb C$. If
--
--   $$
--   a\leq\operatorname{Re}s\leq b,\qquad
--   y:=\operatorname{Im}s\geq Y,\qquad
--   \operatorname{Im}z\geq1,\qquad |z-s|\leq2y^{2/3},
--   $$
--
--   then
--
--   $$
--   \left|
--   \frac{\gamma(z)}
--    {\gamma(s)\exp\!\left(\frac12\operatorname{Log}
--          \left(\frac{s}{2\pi}\right)(z-s)\right)}-1
--   \right|
--   \leq
--   \frac{C}{y}(1+|z-s|)^3
--          \exp\!\left(\frac{|z-s|^2}{y}\right).
--   $$
--
--   Here $\gamma(s)=s(s-1)\pi^{-s/2}\Gamma(s/2)/2$ and $\operatorname{Log}$ is the principal complex logarithm. Both constants may depend on the fixed strip, but are independent of $s$ and $z$ within the stated region.
--
--   This estimate controls the relative error in the leading linear approximation to the gamma factor over a neighborhood whose radius grows like $y^{2/3}$. The quadratic contribution is included in the error bound.
--
--   **Formalization Note.** The expression inside the norm is `gammaLinearError s z`, and `mellinWindow y` is $y^{2/3}$. The theorem is the Riemann specialization of a weakened consequence of the paper's local gamma-ratio estimate, with its error and height quantified explicitly.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, Lemma 5, p. 18; proof using Stirling's formula and a Taylor expansion on pp. 30–32. Specialization to gamma(s)=s(s-1)pi^(-s/2)Gamma(s/2)/2, on fixed vertical strips. Weakened bound obtained by absorbing the quadratic exponential into the error; this is not a verbatim statement of Lemma 5.

import Definitions.Def_DeBruijnNewman_Dobner_Saddle

theorem DeBruijnNewman.Dobner.gammaFactor_local_linearization
    (a b : ℝ) (hab : a < b) :
    ∃ C Y : ℝ, 0 < C ∧ 1 ≤ Y ∧
      ∀ s z : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
        1 ≤ z.im → ‖z - s‖ ≤ 2 * DeBruijnNewman.Dobner.mellinWindow s.im →
          ‖DeBruijnNewman.Dobner.gammaLinearError s z‖ ≤
            C / s.im * (1 + ‖z - s‖) ^ 3 *
              Real.exp (‖z - s‖ ^ 2 / s.im) := by sorry
