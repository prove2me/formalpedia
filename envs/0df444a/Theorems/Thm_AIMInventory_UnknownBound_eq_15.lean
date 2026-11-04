-- Prove2me | Theorems.Thm_AIMInventory_UnknownBound_eq_15
-- name    : AIMInventory.UnknownBound.eq_15
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:31:18.568512+00:00
-- url     : https://prove2.me/theorems/0d5d3754-5725-400f-8689-c4ce8eff87e0
-- title:
--   Proof of Lemma 3, Eq. (15): one-step expected cost inequality for modified AIM
-- statement:
--   Fix a period $t\ge1$ for which the modified AIM projection interval contains the newsvendor quantity: $y^{NV}\le t^{\delta/2}$. Write $\epsilon_t=1/(\max\{b,h\}\sqrt t)$, let $\hat y^\delta_t$ be the target and $H_t(\hat y^\delta_t)$ its sales-based update signal. Then
--
--   $$\mathbb E[Q(\hat y^\delta_t)-Q(y^{NV})]\le\frac{\mathbb E|\hat y^\delta_t-y^{NV}|^2}{2\epsilon_t}-\frac{\mathbb E|\hat y^\delta_{t+1}-y^{NV}|^2}{2\epsilon_t}+\frac{\epsilon_t}{2}\mathbb E|H_t(\hat y^\delta_t)|^2.$$
--
--   This is the one-step comparison used for the rounds after the growing projection interval reaches $y^{NV}$.
--
--   **Formalization Note** The paper applies Appendix A, Eq. (15), to the varying projection intervals of Theorem 7. The comparator is the fixed newsvendor quantity on the rounds where it belongs to the current interval. The common hypotheses are $h,b>0$, $0<\delta<1/2$, finite-mean positive-mean demand, and $\hat y^\delta_1\in[0,1]$.
-- source:
--   Huh & Rusmevichientong, A Non-Parametric Asymptotic Analysis of Inventory Planning with Censored Demand, Math. Oper. Res. (2009), author's manuscript, proof of Theorem 7, p. 12, applying proof of Lemma 3 Eq. (15), p. 16; https://doi.org/10.1287/moor.1080.0355

import Definitions.Def_AIMInventory_UnknownBound_AIM

open MeasureTheory

namespace AIMInventory.UnknownBound

/-- Equation (15) of Appendix A applied to a round of the modified AIM run
whose projection interval contains the newsvendor comparator. -/
theorem eq_15 (P : CappedBaseStock.DemandLaw) (δ b h y₁ : ℝ) (t : ℕ)
    (hδ : δ ∈ Set.Ioo (0 : ℝ) (1 / 2)) (hb : 0 < b) (hh : 0 < h)
    (hy₁ : y₁ ∈ Set.Icc (0 : ℝ) 1) (ht : 1 ≤ t)
    (hcomp : newsvendor P h b ≤ radius δ t) :
    (∫ d : CappedBaseStock.DemandPath,
        (cost P h b (modAimTarget δ b h y₁ d t) - cost P h b (newsvendor P h b))
          ∂CappedBaseStock.demandPathLaw P) ≤
      (∫ d : CappedBaseStock.DemandPath,
          (modAimTarget δ b h y₁ d t - newsvendor P h b) ^ 2
            ∂CappedBaseStock.demandPathLaw P) / (2 * stepSize b h t) -
      (∫ d : CappedBaseStock.DemandPath,
          (modAimTarget δ b h y₁ d (t + 1) - newsvendor P h b) ^ 2
            ∂CappedBaseStock.demandPathLaw P) / (2 * stepSize b h t) +
      stepSize b h t / 2 *
        (∫ d : CappedBaseStock.DemandPath,
          (signal h b (modAimTarget δ b h y₁ d t) (d (t - 1))) ^ 2
            ∂CappedBaseStock.demandPathLaw P) := by sorry

end AIMInventory.UnknownBound
