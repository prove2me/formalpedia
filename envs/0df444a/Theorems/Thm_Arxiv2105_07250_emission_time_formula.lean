-- Prove2me | Theorems.Thm_Arxiv2105_07250_emission_time_formula
-- name    : Arxiv2105_07250.emission_time_formula
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T09:28:42.161797+00:00
-- url     : https://prove2.me/theorems/d35ef8d1-bed3-5ed0-8ea6-209abf346ffb
-- title:
--   Eqs. (A8)-(A11) (as proved): emission time of the retarded wave
-- statement:
--   Let $c>0$, $v\in\mathbb{R}^2$ with $|v|<c$, $x\in\mathbb{R}^2$ and $t\in\mathbb{R}$, and let $q_1,q_2,\mathring t=q_1-\sqrt{q_2}$ be as in (A8), (A9), (A11). Then $q_2\ge0$, and $\mathring t$ is the unique emission time $t'$ with
--
--   $$c\,(t-t')=|x-vt'|.$$
--
--   Moreover, for every $t'$,
--
--   $$\Theta\Big(t-t'-\frac{|x-vt'|}{c}\Big)=\begin{cases}1,& t'\le\mathring t,\\0,& t'>\mathring t.\end{cases}$$
--
--   **Formalization Note** Eq. (A10) as printed compares $t$ with $\mathring t$; the Heaviside factor is a function of the integration variable $t'$ of (A7), and the statement uses $t'$. $\Theta(0)=1$, matching the case split of (A10).
-- source:
--   D. Ayala-Garcia, A. Curtis and M. Branicki, Seismic Interferometry from Correlated Noise Sources, arXiv:2105.07250v2 (2021), claim c022; Appendix A, eqs. (A8)-(A11) and the unnumbered equation after (A11), PDF p. 33

import Mathlib
import Definitions.Def_Arxiv2105_07250_Basic

open MeasureTheory ProbabilityTheory Filter Topology

namespace Arxiv2105_07250

theorem emission_time_formula (c : ℝ) (hc : 0 < c) (v : Plane) (hv : ‖v‖ < c) (x : Plane) (t : ℝ) :
    0 ≤ q2 c t x v ∧
    c * (t - emissionTime c t x v) = ‖x - emissionTime c t x v • v‖ ∧
    (∀ t' : ℝ, c * (t - t') = ‖x - t' • v‖ ↔ t' = emissionTime c t x v) ∧
    (∀ t' : ℝ, heaviside (t - t' - ‖x - t' • v‖ / c) =
      if t' ≤ emissionTime c t x v then 1 else 0) := by sorry

end Arxiv2105_07250
