-- Prove2me | Theorems.Thm_Arxiv1906_02603_rms_echo_square_root_law
-- name    : Arxiv1906_02603.rms_echo_square_root_law
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T06:40:52.914934+00:00
-- url     : https://prove2.me/theorems/f966578f-c0f7-55fa-8de5-f4bef0708c77
-- title:
--   Section II, eq. (6) and Figs. 3-4: the RMS echo grows as $A_0\sqrt{a-a_{\min}}$ for large radius (asymptotic content)
-- statement:
--   Let $\sigma_x,\sigma_y,\sigma_z>0$ and $\kappa_0\neq0$, and let $E(a)$ be the echo energy of eq. (6) of a long cylinder of radius $a$ perpendicular to the GH2 pulse. Then the RMS echo amplitude $\sqrt{E(a)}$ follows the square-root law $A_0\sqrt{a-a_{\min}}$ at large radius: there is $A_0>0$ such that for every threshold $a_{\min}$
--
--   $$\lim_{a\to\infty}\frac{\sqrt{E(a)}}{\sqrt{a-a_{\min}}}=A_0.$$
--
--   The paper uses $A[a]=A_0\sqrt{a-a_{\min}}$ as its model of the amplitude of the echo from a vessel of radius $a$, justified by the asymptotic $|J_1(x)|\sim\sqrt{2/(\pi x)}$.
--
--   **Formalization Note** The paper calls $A_0\sqrt{a-a_{\min}}$ an approximation and shows its quality at small and moderate $a$ only in Figs. 3-4; that part has no precise statement and is not formalized. What is formalized is the large-$a$ behaviour the paper gives as its justification. The limit does not depend on $a_{\min}$.
-- source:
--   K. J. Parker, The first order statistics of backscatter from the fractal branching vasculature, arXiv:1906.02603v3 (2019), claim c002; Section II, text after eq. (6) and Figs. 3-4, PDF p. 9 (relation restated p. 10)

import Mathlib
import Definitions.Def_Arxiv1906_02603_Basic

open MeasureTheory Filter Topology Set

namespace Arxiv1906_02603

theorem rms_echo_square_root_law (sx sy sz kappa0 : ℝ) (hsx : 0 < sx) (hsy : 0 < sy)
    (hsz : 0 < sz) (hkappa0 : kappa0 ≠ 0) :
    ∃ A0 : ℝ, 0 < A0 ∧ ∀ amin : ℝ,
      Tendsto (fun a : ℝ => rmsEcho sx sy sz kappa0 a / Real.sqrt (a - amin)) atTop (𝓝 A0) := by sorry

end Arxiv1906_02603
