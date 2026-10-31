-- Prove2me | Theorems.Thm_FlexLearning_Threshold_threshold_algebra
-- name    : FlexLearning.Threshold.threshold_algebra
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-30T11:46:38.231381+00:00
-- url     : https://prove2.me/theorems/968569b9-4d0e-496f-b2d8-495ad8d0fb94
-- title:
--   Proposition 1, normalised algebraic core — single margin threshold ζ ≈ 0.5904 for V_F(c̃_F) vs V_N (x = 0)
-- statement:
--   Normalised algebraic core of Proposition 1 at $x=0$. For a margin $m\in(0,1]$ and a normalised flexible cost $f\in[0,1)$, put $A=1+m-m^2$. Let
--   $$\varphi(q)=\begin{cases} m^2+q(A-f)-\tfrac A6q^3, & 0\le q\le 1,\\ 1+m-2f+f(2-q)-\tfrac A6(2-q)^3, & 1<q\le 2,\\ 1+m-2f-f(q-2), & q>2,\end{cases}\qquad \nu(m)=\frac{m^2(5-3m)}{A}.$$
--   Here $p U\varphi(Q/U)$ is the two-period flexible profit $v_F(Q)$ with uniform $[0,U]$ demands and price $p$, and $pU\nu(m)$ is $V_N$. Assume the break-even condition $\bar\pi_F=\bar\pi_N$ in normalised form:
--   $$\tfrac23 f(\sqrt{2f}-3)+1=m^2 \ \ (2f\le1),\qquad \tfrac23(1-f)\sqrt{2-2f}=m^2\ \ (2f>1).$$
--
--   **Claim.** There is a single $\zeta\in(0,1)$, independent of $m$ and $f$, such that:
--   - if $m\le\zeta$, then $\nu(m)\le\varphi(q)$ for some $q\ge0$;
--   - if $m>\zeta$, then $\varphi(q)\le\nu(m)$ for all $q\ge0$.
--
--   In words, after scaling, $V_F(\tilde c_F)\ge V_N$ below the margin threshold and $V_F(\tilde c_F)\le V_N$ above it, which is Proposition 1. Numerically $\zeta=\sqrt{1-w_0^2+w_0^3/3}\approx0.5904$, where $w_0\approx0.98476$ is the root in $[0,1]$ of $9w^8-72w^7+196w^6-237w^5+261w^4-372w^3+72w^2+432w-288$.
--
--   **Formalization Note.** This is the purely real-algebraic part of the proof of Proposition 1, isolated from the measure-theoretic computation of $V_N$ and $v_F$.
-- source:
--   Chod, Markakis & Trichakis, On the Learning Benefits of Resource Flexibility, SSRN preprint 3212177 (version of December 6, 2019), p. 12, Proposition 1 (ζ ≈ 0.5904); proof pp. A3–A8 — the comparison of V_F(c̃_F) and V_N after normalising p = U = 1

import Mathlib

namespace FlexLearning.Threshold

theorem threshold_algebra :
    ∃ ζ : ℝ, 0 < ζ ∧ ζ < 1 ∧
      ∀ m f : ℝ, 0 < m → m ≤ 1 → 0 ≤ f → f < 1 →
        (2 * f ≤ 1 → 2 / 3 * f * (Real.sqrt (2 * f) - 3) + 1 = m ^ 2) →
        (1 < 2 * f → 2 / 3 * (1 - f) * Real.sqrt (2 - 2 * f) = m ^ 2) →
        (m ≤ ζ → ∃ q : ℝ, 0 ≤ q ∧
          m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2) ≤
            (if q ≤ 1 then m ^ 2 + q * ((1 + m - m ^ 2) - f) - (1 + m - m ^ 2) * q ^ 3 / 6
             else if q ≤ 2 then 1 + m - 2 * f + f * (2 - q) - (1 + m - m ^ 2) * (2 - q) ^ 3 / 6
             else 1 + m - 2 * f - f * (q - 2))) ∧
        (ζ < m → ∀ q : ℝ, 0 ≤ q →
          (if q ≤ 1 then m ^ 2 + q * ((1 + m - m ^ 2) - f) - (1 + m - m ^ 2) * q ^ 3 / 6
           else if q ≤ 2 then 1 + m - 2 * f + f * (2 - q) - (1 + m - m ^ 2) * (2 - q) ^ 3 / 6
           else 1 + m - 2 * f - f * (q - 2)) ≤
            m ^ 2 * (5 - 3 * m) / (1 + m - m ^ 2)) := by sorry

end FlexLearning.Threshold
