-- Prove2me | Theorems.Thm_DataDrivenRO_FwdBwd_chen_sim_sun
-- name    : DataDrivenRO.FwdBwd.chen_sim_sun
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T14:00:58.80461+00:00
-- url     : https://prove2.me/theorems/618dadd1-ee56-4d48-a4e2-1c886a005cdf
-- title:
--   (22), p. 18 — Chen–Sim–Sun: for independent marginals, VaR^ℙ_ε(v) ≤ Σ μᵢvᵢ + √(2 log(1/ε)(Σ_{vᵢ<0} σ²_{bi}vᵢ² + Σ_{vᵢ≥0} σ²_{fi}vᵢ²))
-- statement:
--   Let $\mathbb P_1,\dots,\mathbb P_d$ be probability measures on $\mathbb R$ with bounded support, with means $\mu_i = \mathbb E^{\mathbb P_i}[\tilde u_i]$, and let $\mathbb P = \mathbb P_1\otimes\cdots\otimes\mathbb P_d$ be the law of a vector $\tilde u$ with independent components. Let $\sigma_{fi},\sigma_{bi}\ge0$ bound the forward and backward deviations (20): $\sigma_f(\mathbb P_i)\le\sigma_{fi}$ and $\sigma_b(\mathbb P_i)\le\sigma_{bi}$. Then for every $\varepsilon\in(0,1)$ and every $v\in\mathbb R^d$,
--   $$\mathrm{VaR}^{\mathbb P}_\varepsilon(v) \le \sum_{i=1}^d \mu_i v_i + \sqrt{2\log(1/\varepsilon)\Big(\sum_{i:v_i<0}\sigma_{bi}^2v_i^2+\sum_{i:v_i\ge0}\sigma_{fi}^2v_i^2\Big)}.$$
--
--   This is the bound of Chen, Sim and Sun (2007) quoted in the paper as (22); Theorem 6 takes its worst case over the confidence region $\mathcal P^{FB}$.
--
--   **Formalization Note** The page states (22) with the deviations $\sigma_f(\mathbb P),\sigma_b(\mathbb P)$ themselves; the statement here uses any upper bounds $\sigma_{fi}\ge\sigma_f(\mathbb P_i)$, $\sigma_{bi}\ge\sigma_b(\mathbb P_i)$. The two forms are equivalent, since the right side is nondecreasing in each $\sigma$ and the bounds may be taken equal to the deviations. Bounded support (the standing assumption of §5.2) makes the deviations finite. Independence is the product measure. Coordinates are 0-based.
-- source:
--   Bertsimas, Gupta & Kallus, Data-Driven Robust Optimization, arXiv:1401.0212v2, (22), p. 18 (quoting Chen, Sim & Sun 2007)

import Mathlib
import Definitions.Def_DataDrivenRO_FwdBwd_Setting

open MeasureTheory

namespace DataDrivenRO.FwdBwd

theorem chen_sim_sun {d : ℕ} (Q : Fin d → Measure ℝ) [∀ i, IsProbabilityMeasure (Q i)]
    (hQ : ∀ i, HasBoundedSupport (Q i)) (σf σb : Fin d → ℝ)
    (hσf : ∀ i, 0 ≤ σf i) (hσb : ∀ i, 0 ≤ σb i)
    (hf : ∀ i, FwdDevLe (Q i) (σf i)) (hb : ∀ i, BwdDevLe (Q i) (σb i))
    (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (v : Fin d → ℝ) :
    VaR (Measure.pi Q) ε v ≤ cssBound (fun i => ∫ t, t ∂(Q i)) σf σb ε v := by sorry

end DataDrivenRO.FwdBwd
