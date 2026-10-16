-- Prove2me | Theorems.Thm_DirectedSearch_Equilibrium_proposition_3_1
-- name    : DirectedSearch.Equilibrium.proposition_3_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T11:01:21.268909+00:00
-- url     : https://prove2.me/theorems/8650a5a0-1595-41e4-b7c7-ad50699cc504
-- title:
--   Proposition 3.1 (item 1, fixed-point form), p. 12 — unique threshold profile equal to the types' expected utilities
-- statement:
--   Consider a two-sided market with finite type sets $\mathcal M$ and $\mathcal W$, life-event rate $\delta>0$, and atomless utility laws $F_{mw}$ with finite mean, and fix any assortments, i.e. meeting rates $\lambda_m(w)\ge0$ and $\lambda_w(m)\ge0$. Then there is exactly one threshold profile $\tau=((\tau_m)_{m\in\mathcal M},(\tau_w)_{w\in\mathcal W})\in\mathbb R^{\mathcal M}\times\mathbb R^{\mathcal W}$ such that every type's threshold equals its expected utility (5):
--   $$\tau_m=\frac{\sum_{w}\lambda_m(w)\int_{\max(\tau_m,\tau_w)}^\infty u\,dF_{mw}}{\delta+\sum_{w}\lambda_m(w)\int_{\max(\tau_m,\tau_w)}^\infty dF_{mw}}\quad(m\in\mathcal M),$$
--   $$\tau_w=\frac{\sum_{m}\lambda_w(m)\int_{\max(\tau_w,\tau_m)}^\infty u\,dF_{mw}}{\delta+\sum_{m}\lambda_w(m)\int_{\max(\tau_w,\tau_m)}^\infty dF_{mw}}\quad(w\in\mathcal W).$$
--
--   This is the existence-and-uniqueness half of the structure theorem for Nash equilibria: for any fixed assortments the model makes a unique prediction of threshold play, which is what makes the platform's design problem over assortments well defined.
--
--   **Formalization Note.** Only the first sentence of item 1 is stated, as a statement about thresholds. "Moreover, this strategy profile is a Nash equilibrium" and item 2 require the agents' Markov decision process of Appendix A.1, which is not formalized. Uniqueness ranges over all real profiles, not only nonnegative ones. Capacity (2) and flow balance (3) are not assumed, since the proposition holds for any fixed assortments. The standing assumptions also include $\alpha_\theta>0$ and finite means, which are implicit in the paper. With empty type sets the unique profile is the empty one.
-- source:
--   Immorlica, Lucier, Manshadi, Wei, Designing Approximately Optimal Search on Matching Platforms, arXiv:2102.09017v2, p. 12, Proposition 3.1, item 1 (first sentence); equation (5), p. 13

import Mathlib
import Definitions.Def_DirectedSearch_Equilibrium_Setting

namespace DirectedSearch.Equilibrium
theorem proposition_3_1 {M W : Type} [Fintype M] [Fintype W] [DecidableEq M] [DecidableEq W]
    (mk : Market M W) (hmk : mk.Standing) (lamM : M → W → ℝ) (lamW : W → M → ℝ)
    (hlamM : ∀ m w, 0 ≤ lamM m w) (hlamW : ∀ w m, 0 ≤ lamW w m) :
    ∃! τ : (M → ℝ) × (W → ℝ),
      (∀ m, τ.1 m = uM mk lamM τ.1 τ.2 m) ∧ (∀ w, τ.2 w = uW mk lamW τ.1 τ.2 w) := by sorry
end DirectedSearch.Equilibrium
