-- Prove2me | Theorems.Thm_FDivToolkit_display_11
-- name    : FDivToolkit.display_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:22:11.367509+00:00
-- url     : https://prove2.me/theorems/061f9c84-b221-46a6-95e7-f6a85162d1fe
-- title:
--   Display (11) — the inverse of the Weibull $H$
-- statement:
--   Let $k>0$, $\theta>\max\{k,1\}$, and let $H$ be the function of (10). The function
--   $$
--   H^{-1}(x)=\begin{cases}\big(\frac\theta kx+1\big)^{k/\theta}-1&x\ge0\\ x&x<0\end{cases}
--   $$
--   of (11) is a two-sided inverse of $H$ on all of $\mathbb R$, and it coincides with the generic inverse $H^{-1}$ of the mission.
--
--   The closed form is what makes the worst-case density (12) explicit.
--
--   Differences from the source:
--   - encoding: "The inverse is given by" (11) → H(H⁻¹x) = x and H⁻¹(Hy) = y for all x, y, and Hinv (weibullH k θ) = weibullHinv k θ; reason: this is what being the inverse means; L = −∞ makes H a bijection of ℝ
-- source:
--   Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), display (11), §3.1, p.12

import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_weibullH

namespace FDivToolkit

/-- Display (11), Kruse, Schneider & Schweizer, SSRN 3680475 (Aug 25, 2020), §3.1, p.12: the inverse
of the Weibull `H` of (10) is the function of (11). As `L = −∞`, `H` is a bijection of `ℝ`, so this is
a two-sided inverse on all of `ℝ`, and it is the generic `H⁻¹` used in (5), (6) and (7). -/
theorem display_11 {k θ : ℝ} (hk : 0 < k) (hθ : max k 1 < θ) :
    (∀ x : ℝ, weibullH k θ (weibullHinv k θ x) = x) ∧
    (∀ y : ℝ, weibullHinv k θ (weibullH k θ y) = y) ∧
    Hinv (weibullH k θ) = weibullHinv k θ := by sorry

end FDivToolkit
