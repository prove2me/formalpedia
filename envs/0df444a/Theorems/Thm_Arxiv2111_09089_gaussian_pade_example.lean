-- Prove2me | Theorems.Thm_Arxiv2111_09089_gaussian_pade_example
-- name    : Arxiv2111_09089.gaussian_pade_example
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T10:25:48.937831+00:00
-- url     : https://prove2.me/theorems/24384091-6297-5b77-b228-324e9a71afac
-- title:
--   Section II-A example: two Padé approximations of $e^{-x^2}$ (as corrected)
-- statement:
--   Let $f(x)=e^{-x^2}$, let $f_T(x)=1-x^2+x^4/2-x^6/6$ be its Taylor polynomial of order $6$ about $0$, and let
--
--   $$f_{P1}(x)=\frac{1-x^2/3}{1+2x^2/3+x^4/6},\qquad f_{P2}(x)=\frac1{1+x^2+x^4/2}.$$
--
--   Then, as $x\to0$:
--
--   1. $f(x)-f_T(x)=O(x^8)$;
--   2. $f_{P1}(x)-f_T(x)=O(x^8)$, so $f_{P1}$ agrees with the Taylor expansion through order $6$;
--   3. $f_{P2}(x)-(1-x^2+x^4/2)=O(x^6)$, but $\big(f_{P2}(x)-f_T(x)\big)/x^6\to1/6$, so $f_{P2}$ agrees with the Taylor expansion through order $4$ and not through order $6$.
--
--   As $|x|\to\infty$:
--
--   4. $f_T(x)\to-\infty$;
--   5. $x^2f_{P1}(x)\to-2$ and $x^4f_{P2}(x)\to2$, so $f_{P2}$ decays fastest of the three approximations;
--   6. $x^nf(x)\to0$ for every $n\in\mathbb N$.
--
--   The example shows how the degree difference of a Padé approximation sets its decay at infinity.
--
--   **Formalization Note** The paper says that both Padé approximations are based on the same Taylor expansion and that $f_{P2}$ is the globally best. No error measure is given for "globally best", so that comparison is not stated. Item 3 records that $f_{P2}$ matches the Taylor expansion only through order $4$.
-- source:
--   Y. Hadad, On the use of the Padé-Fourier approximation in fast evaluation of the Green's function of layered media, arXiv:2111.09089v1 (2021), claim c018; Section II-A, illustrative example and Fig. 2, PDF p. 2

import Mathlib
import Definitions.Def_Arxiv2111_09089_Basic

open Complex MeasureTheory Filter Topology Asymptotics

namespace Arxiv2111_09089

theorem gaussian_pade_example :
    (fun x : ℝ => Real.exp (-x ^ 2) - gaussTaylor x) =O[𝓝 0] (fun x => x ^ 8) ∧
    (fun x : ℝ => padeP1 x - gaussTaylor x) =O[𝓝 0] (fun x => x ^ 8) ∧
    (fun x : ℝ => padeP2 x - (1 - x ^ 2 + x ^ 4 / 2)) =O[𝓝 0] (fun x => x ^ 6) ∧
    Tendsto (fun x : ℝ => (padeP2 x - gaussTaylor x) / x ^ 6) (𝓝[≠] 0) (𝓝 (1 / 6)) ∧
    Tendsto gaussTaylor (cocompact ℝ) atBot ∧
    Tendsto (fun x : ℝ => x ^ 2 * padeP1 x) (cocompact ℝ) (𝓝 (-2)) ∧
    Tendsto (fun x : ℝ => x ^ 4 * padeP2 x) (cocompact ℝ) (𝓝 2) ∧
    ∀ n : ℕ, Tendsto (fun x : ℝ => x ^ n * Real.exp (-x ^ 2)) (cocompact ℝ) (𝓝 0) := by sorry

end Arxiv2111_09089
