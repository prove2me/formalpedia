-- Prove2me | Theorems.Thm_DualSSD_Duality_ssd_iff_secondQuantile_ge
-- name    : DualSSD.Duality.ssd_iff_secondQuantile_ge
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:39:52.224064+00:00
-- url     : https://prove2.me/theorems/ff3ddaf9-b096-4d10-9280-6e5d241e0fce
-- title:
--   Theorem 3.2 — $X\succeq_{SSD}Y$ iff $F_X^{(-2)}(p)\ge F_Y^{(-2)}(p)$ for all $0\le p\le1$
-- statement:
--   Let $X$ and $Y$ be random variables on a common probability space with $\mathbb E|X|<\infty$ and $\mathbb E|Y|<\infty$. Then
--   $$X\succeq_{SSD}Y\iff F_X^{(-2)}(p)\ge F_Y^{(-2)}(p)\quad\text{for all }0\le p\le 1.$$
--   Here $X\succeq_{SSD}Y$ means $F_X^{(2)}(\eta)\le F_Y^{(2)}(\eta)$ for all $\eta\in\mathbb R$, with $F_X^{(2)}(\eta)=\int_{-\infty}^\eta\mathbb P\{X\le\xi\}\,d\xi$, and $F_X^{(-2)}(p)=\int_0^pF_X^{(-1)}(\alpha)\,d\alpha$ is the absolute Lorenz curve, $F_X^{(-1)}$ being the left quantile function.
--
--   Second-degree stochastic dominance is therefore dominance of absolute Lorenz curves: $X$ is preferred by every risk-averse decision maker exactly when, for every fraction $p$ of worst outcomes, the integrated worst-case outcomes of $X$ are at least those of $Y$. At $p=1$ this contains $\mathbb EX\ge\mathbb EY$.
--
--   **Formalization Note** Integrability of $X$ and $Y$ is the paper's standing assumption for $F^{(-2)}$ (p. 65). The absolute Lorenz curves are compared in `EReal`; on $[0,1]$ both are finite.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 66, Theorem 3.2

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance
import Definitions.Def_DualSSD_Duality_secondQuantile

namespace DualSSD.Duality

open MeasureTheory

/-- Theorem 3.2 (Ogryczak–Ruszczyński 2002, §3, p. 66): for random variables `X, Y` on one
probability space with `E|X| < ∞` and `E|Y| < ∞`,
`X ⪰_SSD Y ⇔ F_X^(−2)(p) ≥ F_Y^(−2)(p)` for all `0 ≤ p ≤ 1`. -/
theorem ssd_iff_secondQuantile_ge {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X Y : Ω → ℝ)
    (hX : Integrable X P) (hY : Integrable Y P) :
    Shared.SSD P X Y ↔ ∀ p ∈ Set.Icc (0 : ℝ) 1, secondQuantile P Y p ≤ secondQuantile P X p := by sorry

end DualSSD.Duality
