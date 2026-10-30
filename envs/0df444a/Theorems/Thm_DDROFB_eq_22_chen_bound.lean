-- Prove2me | Theorems.Thm_DDROFB_eq_22_chen_bound
-- name    : DDROFB.eq_22_chen_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T03:08:02.679681+00:00
-- url     : https://prove2.me/theorems/375074cc-a086-419e-9823-6742d4e72d36
-- title:
--   Eq. (22): Chen–Sim–Sun deviation bound on $\mathrm{VaR}^{\mathbb P}_\epsilon$
-- statement:
--   Let $\mathbb P$ be a probability measure on $\mathbb R^d$ with independent components $\tilde u_1,\dots,\tilde u_d$, and suppose that every forward and backward deviation $\sigma_f(\mathbb P_i)$, $\sigma_b(\mathbb P_i)$ (20) of the marginals is finite (in particular every mean $\mathbb E^{\mathbb P}[\tilde u_i]$ exists). Then for every $0<\epsilon<1$ and every $v \in \mathbb R^d$,
--
--   $$
--   \mathrm{VaR}^{\mathbb P}_\epsilon(v) \;\le\; \sum_{i=1}^d \mathbb E^{\mathbb P}[\tilde u_i]\, v_i + \sqrt{2\log(1/\epsilon)\Bigl(\sum_{i : v_i<0} \sigma_b(\mathbb P_i)^2 v_i^2 + \sum_{i : v_i \ge 0} \sigma_f(\mathbb P_i)^2 v_i^2\Bigr)} .
--   $$
--
--   The paper cites this bound from Chen, Sim and Sun (Operations Research 55(6), 2007) and uses it in Step 2 of its schema: taking its worst case over the confidence region $\mathcal P^{FB}$ gives the support function of $\mathcal U^{FB}_\epsilon$.
--
--   Differences from the source:
--   - reading: the mean and deviations for P are known → every fwdDev (marginal P i) and bwdDev (marginal P i) is finite (≠ ⊤); reason: a deviation is "known" as a real number exactly when it is finite; a finite deviation entails that the mean exists
--   - encoding: the marginals are independent → HasIndepComponents P (mutual independence of the coordinate maps); reason: mutual independence of the components is independence of the marginals in the paper's sense
--   - encoding: level ϵ → hypotheses 0 < ε and ε < 1; reason: the schema's range 0 < ϵ < 1 (p. 10); for ε ≥ 1, log(1/ε) ≤ 0 and the square root in the formula is not defined
-- source:
--   Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (22), p. 18 (unnumbered result attributed to Chen et al. 2007)

import Mathlib
import Definitions.Def_DDROFB_VaR
import Definitions.Def_DDROFB_fwdDev
import Definitions.Def_DDROFB_bwdDev
import Definitions.Def_DDROFB_marginal
import Definitions.Def_DDROFB_HasIndepComponents
import Definitions.Def_DDROFB_chenBound
open MeasureTheory

namespace DDROFB

/-- **The deviation bound (22) of Chen, Sim and Sun (2007) on Value at Risk.**
Bertsimas, Gupta, Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, eq. (22), p. 18
(unnumbered result, cited from Chen et al. 2007): "When the mean and deviations for `P` are known
and the marginals are independent, Chen et al. (2007) prove
`VaR^P_ϵ(v) ≤ Σ_{i=1}^d E^P[ũ_i] v_i + √(2 log(1/ϵ) (Σ_{i:v_i<0} σ²_{bi}(P) v²_i +
Σ_{i:v_i≥0} σ²_{fi}(P) v²_i))`."

**Formalization Note.** `P` is a probability measure on `ℝ^d` with independent components.
"The mean and deviations for `P` are known" is read as: every forward and backward deviation (20)
of every marginal is finite (`≠ ⊤`); by the definition of `fwdDev`, finiteness entails that every
mean exists. The level is `0 < ε < 1`, the range of the schema (p. 10); for `ε ≥ 1` the term
`log(1/ε) ≤ 0` makes the radicand negative and the printed bound meaningless. No bounded-support
assumption is made. -/
theorem eq_22_chen_bound {d : ℕ} (P : Measure (EuclideanSpace ℝ (Fin d)))
    [IsProbabilityMeasure P] (hind : HasIndepComponents P)
    (hdev : ∀ i, fwdDev (marginal P i) ≠ ⊤ ∧ bwdDev (marginal P i) ≠ ⊤)
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : EuclideanSpace ℝ (Fin d)) :
    VaR P ε v ≤ chenBound P ε v := by sorry

end DDROFB
