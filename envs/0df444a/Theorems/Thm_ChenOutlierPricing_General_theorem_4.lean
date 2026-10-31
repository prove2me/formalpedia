-- Prove2me | Theorems.Thm_ChenOutlierPricing_General_theorem_4
-- name    : ChenOutlierPricing.General.theorem_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-10-30T06:45:20.650945+00:00
-- url     : https://prove2.me/theorems/20492b6d-017b-42eb-9407-71049910b8b3
-- title:
--   Theorem 4 — adaptive robust regret for general inventory
-- statement:
--   Fix the full pricing model of §3, with (A1)–(A2), $0<x_0\le1$, real initial inventory $x_0T$, continuous nonnegative price interval, and α>0 from (A3). Suppose $p^c\ne p^o$. The seller has two feasible measurable input-policy families. In the regime $p^c<p^o$, $\pi^o$ has regret $\widetilde O(\varepsilon T+\sqrt{T''})$ for every lower-price input between $p^c$ and $p^o$; in the regime $p^c>p^o$, $\pi^c$ has the same regret guarantee. These are uniform contracts over positive eligible nominal subroutine horizons H≤2T, restarts and all admissible demand/noise laws; the absolute corruption budget is εT, not εT″. The policies receive no typical demand curve, ε or true regime.
--   Then the specified Algorithm 5, with the explicit zero/singleton completion of Algorithm 4, satisfies
--   $$R_{T,\varepsilon T}(\mathrm{Algorithm\ 5};f_0,x_0)=\widetilde O(\varepsilon T+\sqrt T)$$
--   for all sufficiently large T, uniformly over $0\le\varepsilon\le T^{-\alpha}$ and all admissible adaptive adversaries and price-conditioned mean-zero noise laws. Constants and polynomial/logarithmic degrees are chosen with the model and policies fixed, before T and the environment. The envelope contains the printed parameters $p^o,p^c,\underline p,\overline p,\underline L_p,\overline L_p,M^2,\sigma^2$ and log T. Both strict inventory regimes remain in this single theorem; $p^c=p^o$ remains excluded. Regret is the fluid typical-demand benchmark minus expected actual revenue, including customer and seller randomness. The algorithm computes the branch and both estimates from observations; it neither receives nor assumes the correct regime.
--
--   Differences from the source:
--   - reading: the display says Alg.6 while the prose says meta algorithm 5 → the explicitly defined Algorithm 5; reason: Algorithm 5 is printed next to the theorem and there is no Algorithm 6
--   - encoding: periods numbered 1 through T with remaining inventory → elapsed indices 0 through T-1 and recursively computed real stock; reason: a bijective time reindexing preserves every price, censored sale and revenue
--   - encoding: randomized seller policies and adaptive outlier curves with E[ξ_t | p_t] = 0 → an independent private uniform tape, arbitrary exogenous probability space, observed-history policy maps, and zero noise integrals on every price-measurable event; reason: random seeds implement stochastic decisions; integrable noise and measurable observations make the printed conditional expectation well defined without a martingale-difference or independent-noise assumption
--   - reading: Algorithm 4 leaves zero/singleton grids undefined although Algorithm 5 reaches them → empty exploration returns both lower endpoints; a singleton grid offers and returns the lower endpoint; valid ties use the smallest index; reason: total completion of omitted cases preserves all defined executions and retains the printed T₀ normalization; no event is conditioned away
--   - encoding: tilde O with fixed model parameters and sufficiently large T → positive coefficient, polynomial degree, logarithmic degree and horizon threshold precede every horizon, ε and environment; the rate is C times parameterScale^d times (1+log T)^k times (εT+sqrt H); reason: this makes the fixed-model upper-bound quantifiers explicit, keeps the printed parameter list and uses the absolute subroutine corruption budget εT
--   - encoding: Algorithm 5 chooses an exploration set before running its two routines → private presampling of the complete truncated epoch set, disjoint tape coordinates for grid draws and each subroutine; reason: the realized cardinality is needed to form the source grid; no private schedule is an adversary input
--   - reading: the subroutine horizon is implicit in run on the exploitation periods with allocation x₀T(ζ) → initialize the subroutine with nominal horizon T(ζ) and allocation x₀T(ζ), advancing it only on exploitation observations; reason: this preserves the printed nominal stock and permits the source regret contract at its initialization horizon; physical stock remains shared
--   - reading: offer the upper price in the rest of the epoch if the designated inventory runs out → check cumulative exploitation sales before each exploitation offer; censor each sale by the shared physical stock; reason: the footnote specifies subsequent price decisions while equation (2) specifies the physical-sales censor; no separate within-period nominal-quota censor is stated
-- source:
--   Chen and Wang, DOI 10.1287/opre.2022.2280, supplied source.pdf, pp. 31–32, Theorem 4

import Definitions.Def_ChenOutlierPricing_General_Bounds

namespace ChenOutlierPricing.General

/-- Chen and Wang, source.pdf pp. 31–32, Theorem 4, both inventory regimes. -/
theorem theorem_4 (m : Model) (hm : Assumptions m) (α : ℝ) (hα : 0 < α)
    (πo : ℝ → Policy) (πc : Policy)
    (ho : ∀ lower ∈ Set.Icc m.band.lo m.band.hi, PolicyAdmissible m.band (πo lower))
    (hc : PolicyAdmissible m.band πc)
    (hneq : clearance m ≠ optimum m) (hinput : InputBounds m α πo πc) :
    MetaBound m α πo πc := by sorry

end ChenOutlierPricing.General
