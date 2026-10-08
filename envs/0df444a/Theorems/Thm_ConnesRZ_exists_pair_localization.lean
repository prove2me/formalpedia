-- Prove2me | Theorems.Thm_ConnesRZ_exists_pair_localization
-- name    : ConnesRZ.exists_pair_localization
-- status  : Proved
-- author  : @waitingintime
-- created : 2026-10-06T20:39:40.054995+00:00
-- url     : https://prove2.me/theorems/9787a598-d9e2-4196-9a60-3c7e0cda7972
-- title:
--   Burnol localization: interpolate an off-line zero pair and suppress the spectral complement
-- statement:
--   Let $\rho_0$ be a zero of the Riemann zeta function with $0<\operatorname{Re}\rho_0<1$ and $\operatorname{Re}\rho_0\ne1/2$. Put $\sigma_0=1-\bar\rho_0$, and use the shifted transform
--   $$\widehat g(z)=\int_{\mathbb R}g(t)e^{(z-1/2)t}\,dt.$$
--   Then $\sigma_0$ is also a critical-strip zero, both zeros have positive multiplicity, and there is a smooth compactly supported $g:\mathbb R\to\mathbb C$ satisfying
--   $$\widehat g(\rho_0)=1,\qquad\widehat g(\sigma_0)=-1.$$
--   The complementary real spectral family is unconditionally summable with a sum $r<1$:
--   $$\sum_{\rho\notin\{\rho_0,\sigma_0\}}\operatorname{Re}\!\left(m_\rho\widehat g(\rho)\overline{\widehat g(1-\bar\rho)}\right)=r<1.$$
--   The sum runs over distinct critical-strip zeros and includes their analytic multiplicities as weights. In particular it does not assume that the chosen zeros are simple.
--
--   This is the qualitative localization step in Burnol's proof of Weil's positivity criterion: it separates a selected pair from the remaining divisor. No common support bound is prescribed, and no positivity or RH hypothesis is used. It provides the analytic child needed to connect the mission's spectral expansion to its main implication.
--
--   **Formalization Note.** The complementary sum is represented by a `HasSum` whose selected-pair terms are replaced by zero. The threshold $1$ is a fixed positive tolerance, obtained by choosing the convolution power sufficiently large. The multiplicity-weighted contribution of the selected pair is $-(m_{\rho_0}+m_{\sigma_0})$, rather than using a simple-zero normalization.
-- source:
--   Jean-Francois Burnol, The Explicit Formula in simple terms, https://arxiv.org/abs/math/9810169v2 , section "Weil’s positivity criterion and stochastic processes", pp. 5-6: finite Mellin interpolation, cancellation of the finitely many exceptional zeros, and convolution powers with complementary contribution O(4^{-N}). This statement is the resulting fixed-tolerance localization consequence, translated to additive coordinates with a half-shift; multiplicities are retained explicitly.

import Definitions.Def_ConnesRZ_weil_defs

open Complex MeasureTheory

namespace ConnesRZ

theorem exists_pair_localization :
∀ s : ℂ, IsCriticalZero s → s.re ≠ 1 / 2 →
      ∃ g : ℝ → ℂ, IsTest g ∧
        IsCriticalZero (1 - (starRingEnd ℂ) s) ∧
        0 < zeroMult s ∧ 0 < zeroMult (1 - (starRingEnd ℂ) s) ∧
        mellinHat g s = 1 ∧ mellinHat g (1 - (starRingEnd ℂ) s) = -1 ∧
        ∃ r : ℝ, r < 1 ∧ HasSum
          (fun ρ : {z : ℂ // IsCriticalZero z} =>
            if ρ.1 = s ∨ ρ.1 = 1 - (starRingEnd ℂ) s then 0 else
              ((zeroMult ρ.1 : ℂ) * (mellinHat g ρ.1 *
                (starRingEnd ℂ) (mellinHat g (1 - (starRingEnd ℂ) ρ.1)))).re) r := by sorry

end ConnesRZ
