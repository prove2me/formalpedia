-- Prove2me | Theorems.Thm_BroughanRH_verjovsky
-- name    : BroughanRH.verjovsky
-- status  : Open
-- author  : @liuyao
-- created : 2026-11-23T04:26:31.617513+00:00
-- url     : https://prove2.me/theorems/8b1aafb9-8965-439a-becf-5cb7f66b678e
-- title:
--   Verjovsky’s totient-weighted discrete measures
-- statement:
--   For every order $2\le r\le\infty$ and every real $C^r$ test function compactly supported in $(0,\infty)$, the totient-weighted sum has error $o(y^{3/4-\varepsilon})$ as $y\downarrow0$. Its limit is $6\pi^{-2}\int_0^\infty u f(u)\,du$. [Source](https://doi.org/10.2996/kmj/1138040054).
-- source:
--   Kevin Broughan, Equivalents of the Riemann Hypothesis, II Thm. 10.10. https://www.cambridge.org/core/books/equivalents-of-the-riemann-hypothesis/095D9AC2C5E0A74FF24389AD0D9BD458

import Mathlib

namespace BroughanRH

theorem verjovsky :
    ∀ r : ℕ∞, 2 ≤ r → ∀ f : ℝ → ℝ, ContDiff ℝ r f → HasCompactSupport f → tsupport f ⊆ Set.Ioi 0 →
      let m (y : ℝ) := ∑' k : ℕ, y * ((k+1).totient : ℝ) * f (Real.sqrt y * (k+1 : ℕ))
      let m₀ := (6 / Real.pi^2) * (∫ x in Set.Ioi (0 : ℝ), x * f x)
      ∀ ε : ℝ, 0 < ε → Asymptotics.IsLittleO (nhdsWithin 0 (Set.Ioi 0))
        (fun y : ℝ => m y - m₀) (fun y : ℝ => y^(3/4-ε)) := by sorry

end BroughanRH
