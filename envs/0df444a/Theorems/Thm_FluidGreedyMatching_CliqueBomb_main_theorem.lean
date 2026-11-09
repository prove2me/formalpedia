-- Prove2me | Theorems.Thm_FluidGreedyMatching_CliqueBomb_main_theorem
-- name    : FluidGreedyMatching.CliqueBomb.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:58:43.597294+00:00
-- url     : https://prove2.me/theorems/e2069ae1-5010-4c14-9b11-1d8627512935
-- title:
--   Theorem 1.4 — MRG on general graphs
-- statement:
--   Run MRG on the Double-Bomb with hub cliques $S_n^K(1)$, with $n$ vertices in each of its six classes. Let $\rho$ be the exact elementary-function integral defined by Eq. (5.4) at $\sigma=1$, including the terminal term $q_*^2$, divided by three. The integrand is integrable on $[1,\infty)$, and
--   $$\lim_{n\to\infty}\frac{\mathbb E|M_{\rm MRG}(S_n^K(1))|}{\nu(S_n^K(1))}=\rho,\qquad
--   \rho<\frac{6569}{10000},\qquad
--   \inf_{G:\nu(G)>0}\frac{\mathbb E|M_{\rm MRG}(G)|}{\nu(G)}\le\frac{6569}{10000}.$$
--
--   The infimum covers all finite simple graphs. The exact limit and rigorous rational enclosure are both obligations of this theorem. The decimal with ellipses in the source describes this integral; it is not an exact terminating rational. Neither a stochastic limit nor a numerical certificate is assumed.
--
--   Differences from the source:
--   - encoding: positive sizes and the worst-case ratio over finite simple graphs → size j+1 and an infimum over all graphs on Fin N with positive computed matching number; reason: all positive sizes and every finite graph up to relabeling are covered
--   - encoding: the explicit integral rho_K(1) and the decimal upper bound from its proof → the real integral together with integrability, strict rho < 6569/10000, and the non-strict approximation bound; reason: these retain the exact integral and the strict numerical enclosure used on p. 25, without assuming its certificate
-- source:
--   Sayan Mukherjee, Fluid Limits and Upper Bounds for Randomized Greedy Matching, STOC 2027 submission #492 (October 2026), Theorem 1.4, p. 5; Eq. (5.4), Section 5.4 and footnote 2, p. 25

import Mathlib
import Definitions.Def_FluidGreedyMatching_CliqueBomb_DoubleBomb
import Definitions.Def_FluidGreedyMatching_CliqueBomb_ExactConstant

set_option autoImplicit false
open MeasureTheory Filter
open scoped Topology

namespace FluidGreedyMatching.CliqueBomb

/-- Theorem 1.4, p. 5, with its exact integral from Eq. (5.4), p. 25.
There is no assumed fluid limit, count certificate, or numerical certificate. -/
theorem main_theorem :
    IntegrableOn exactIntegrand (Set.Ici (1 : ℝ)) volume ∧
    Tendsto (bombRatio 1 true) atTop (𝓝 rho) ∧
    rho < (6569 : ℝ) / 10000 ∧
    approximationRatio ≤ (6569 : ℝ) / 10000 := by sorry

end FluidGreedyMatching.CliqueBomb
