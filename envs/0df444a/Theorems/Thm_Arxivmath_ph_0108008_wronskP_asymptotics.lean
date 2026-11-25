-- Prove2me | Theorems.Thm_Arxivmath_ph_0108008_wronskP_asymptotics
-- name    : Arxivmath_ph_0108008.wronskP_asymptotics
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T19:36:07.187898+00:00
-- url     : https://prove2.me/theorems/b9cce4c7-0c4a-4863-9879-45e31ae176f6
-- title:
--   Section 2: $p(r)=-r^2/5+o(r^2)$ as $r\to0$ and $p(r)\to1$ as $r\to\infty$
-- statement:
--   For the function $p$ of Section 2:
--   - $p(r)=-\frac{r^2}{5}+o(r^2)$ as $r\to0^+$, so $p(r)<0$ for all sufficiently small $r>0$;
--   - $p(r)\to1$ as $r\to\infty$, so $p(r)>0$ for all sufficiently large $r$.
-- source:
--   A. G. Ramm, A counterexample to the uniqueness result of Cox and Thompson, arXiv:math-ph/0108008v1, claim c004; Section 2, sentence after the formula for p(r), PDF p. 2

import Mathlib
import Definitions.Def_Arxivmath_ph_0108008_Basic

open MeasureTheory Filter Topology Real

namespace Arxivmath_ph_0108008

theorem wronskP_asymptotics :
    (fun r => wronskP r + r ^ 2 / 5) =o[𝓝[>] 0] (fun r => r ^ 2) ∧
    (∀ᶠ r in 𝓝[>] 0, wronskP r < 0) ∧
    Tendsto wronskP atTop (𝓝 1) ∧ (∀ᶠ r in atTop, 0 < wronskP r) := by sorry

end Arxivmath_ph_0108008
