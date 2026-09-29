-- Prove2me | Theorems.Thm_DeBruijnNewman_Dobner_mellin_contour_remainder
-- name    : DeBruijnNewman.Dobner.mellin_contour_remainder
-- status  : Proved
-- author  : @adobner
-- created : 2026-09-25T00:03:49.06901+00:00
-- url     : https://prove2.me/theorems/29b80ae2-e979-4441-8e6c-148028edceb0
-- title:
--   The normalized remainder outside a fixed coefficient's central saddle segment
-- statement:
--   Fix $t<0$, real numbers $a<b$, and one positive integer $N$. Set $T=|t|$. Let
--
--   $$
--   B_{t,N}(s)=\frac1{\sqrt{\pi T}}\int_{\mathbb R}
--   \gamma(2+iv)\exp\!\left(\frac{(J_t(s)-(2+iv))^2}{T}
--                            -(2+iv)\log N\right)\,dv,
--   $$
--
--   and let $B^{\mathrm{cen}}_{t,N}(s)$ denote the same normalized integrand integrated over the upward finite segment
--
--   $$
--   z(u)=s+\frac{T\log N}{2}+iu,\qquad
--   -y^{2/3}\leq u\leq y^{2/3},\qquad y=\operatorname{Im}s.
--   $$
--
--   There exist constants $C>0$ and $Y\geq1$ such that, for all $s\in\mathbb C$ with $a\leq\operatorname{Re}s\leq b$ and $y\geq Y$,
--
--   $$
--   \left|\frac{B_{t,N}(s)-B^{\mathrm{cen}}_{t,N}(s)}
--                    {\gamma_t(s)}\right|
--   \leq C\exp\!\left(-\frac{y^{4/3}}{40T}\right).
--   $$
--
--   The normalization is
--
--   $$
--   J_t(s)=s+\frac T4\operatorname{Log}\frac{s}{2\pi},\qquad
--   \gamma_t(s)=\gamma(s)\exp\!\left(\frac{(s-J_t(s))^2}{T}\right),\qquad
--   \gamma(s)=\frac{s(s-1)}2\pi^{-s/2}\Gamma(s/2).
--   $$
--
--   The constants may depend on $t,a,b,N$, but are independent of $s$ above the chosen height. The estimate includes normalization by $\gamma_t(s)$; it bounds the total contribution remaining after replacing the original vertical contour by the central segment.
--
--   **Formalization Note.** The three functions in the quotient are `mellinTerm t s n`, `centralMellinTerm t s n`, and `gammaT t s`, with $N=n+1$. The fixed-index leading saddle is used, rather than the paper's corrected saddle. No uniformity in a growing range of indices is asserted.
-- source:
--   Alexander Dobner, A proof of Newman's conjecture for the extended Selberg class, arXiv:2005.05142v2 (10 January 2026), https://arxiv.org/abs/2005.05142v2, proof of Lemma 4, pp. 19–22: the finite contour shift, H1/H2 and V1/V2 estimates using Lemma 6, and the gamma_t lower bound (27), p. 22. Fixed-strip, fixed-index leading-saddle variant; normalized exponential rate weakened from 1/(20|t|) before normalization to 1/(40|t|).

import Definitions.Def_DeBruijnNewman_Dobner_Saddle

theorem DeBruijnNewman.Dobner.mellin_contour_remainder
    (t : ℝ) (ht : t < 0) (a b : ℝ) (hab : a < b) (n : ℕ) :
    ∃ C Y : ℝ, 0 < C ∧ 1 ≤ Y ∧
      ∀ s : ℂ, a ≤ s.re → s.re ≤ b → Y ≤ s.im →
        ‖(DeBruijnNewman.Dobner.mellinTerm t s n -
            DeBruijnNewman.Dobner.centralMellinTerm t s n) /
              DeBruijnNewman.Dobner.gammaT t s‖ ≤
          C * Real.exp (-(s.im ^ (4 / 3 : ℝ)) / (40 * |t|)) := by sorry
