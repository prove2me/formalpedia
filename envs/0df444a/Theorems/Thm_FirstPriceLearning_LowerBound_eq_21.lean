-- Prove2me | Theorems.Thm_FirstPriceLearning_LowerBound_eq_21
-- name    : FirstPriceLearning.LowerBound.eq_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T10:14:27.31912+00:00
-- url     : https://prove2.me/theorems/0d71a8a4-e173-4d63-8e83-c8993250cf7c
-- title:
--   (21), p. 37 — two-point reduction: $\tfrac12E_{G_1}[R_T]+\tfrac12E_{G_2}[R_T]\ge\tfrac{\Delta T}{3}(1-\|P_1^{\otimes T}-P_2^{\otimes T}\|_{\mathrm{TV}})$
-- statement:
--   Let $\Delta\in(0,1/4)$ and $T\in\mathbb N$, let $G_1,G_2$ be the two HOB laws of the two-point construction, and let $P_i^{\otimes T}$ be the law of $(m_1,\dots,m_T)$ when the HOBs are iid from $G_i$. Let the values be $v_t\equiv1$ and let the HOBs be revealed at the end of every round (full information). Then for every policy $\pi$, randomized or not,
--
--   $$
--   \frac12\,\mathbb E_{G_1}[R_T(\pi;v)]+\frac12\,\mathbb E_{G_2}[R_T(\pi;v)]\ \ge\ \frac{\Delta T}{3}\Bigl(1-\bigl\|P_1^{\otimes T}-P_2^{\otimes T}\bigr\|_{\mathrm{TV}}\Bigr).
--   $$
--
--   This is the reduction of the regret lower bound to a testing problem between $G_1$ and $G_2$: a policy with small regret under both laws would have to distinguish them from the observed HOBs.
--
--   **Formalization Note** Only the two endpoints of the printed chain (21) are stated; the first step "$\sup_G\mathbb E_G[R_T]\ge$ the average" and the intermediate lines are part of the proof. The expectation integrates over the policy's internal randomness as well as the HOBs; the per-round step (b) applies after integrating out that randomness.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 37, App. B, (21)

import Mathlib
import Definitions.Def_FirstPriceLearning_LowerBound_TVDist
import Definitions.Def_FirstPriceLearning_LowerBound_Model
import Definitions.Def_FirstPriceLearning_LowerBound_TwoPointLaws

open MeasureTheory

namespace FirstPriceLearning.LowerBound

/-- arXiv:2003.09795v7, App. B, (21), p. 37 (two-point reduction, endpoints of the chain): for every
`Δ ∈ (0, 1/4)`, every horizon `T` and every randomized full-information policy `π`,
`(1/2) E_{G₁}[R_T(π; v)] + (1/2) E_{G₂}[R_T(π; v)] ≥ (ΔT/3)(1 − ‖P₁^{⊗T} − P₂^{⊗T}‖_TV)`, where `v_t ≡ 1`
and `P_i^{⊗T}` is the law of `(m_1, …, m_T)` with `m_t` iid from `G_i`. -/
theorem eq_21 {T : ℕ} {U : Type} [MeasurableSpace U] (π : FullInfoPolicy T U)
    (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1 / 4) :
    Δ * T / 3 * (1 - tvDist (Measure.pi fun _ : Fin T => lawG1 Δ)
        (Measure.pi fun _ : Fin T => lawG2 Δ)) ≤
      1 / 2 * expectedRegret π (lawG1 Δ) + 1 / 2 * expectedRegret π (lawG2 Δ) := by sorry

end FirstPriceLearning.LowerBound
