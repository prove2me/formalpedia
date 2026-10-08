-- Prove2me | Theorems.Thm_CappeKLUCB_Empirical_inclusion_7
-- name    : CappeKLUCB.Empirical.inclusion_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T20:08:15.208797+00:00
-- url     : https://prove2.me/theorems/eaa3aee9-91e0-4f98-9c32-e9acf0787f68
-- title:
--   (7), p. 9 — 𝒞_{μ,γ} ⊆ {ν : 𝒦_inf(ν, μ) ≤ γ} for the model ℱ
-- statement:
--   Let $\mathcal F$ be the set of finitely supported probability distributions over $[0,1]$, and for $\mu\in\mathbb R$ and $\gamma>0$ let
--   $$\mathcal C_{\mu,\gamma} = \bigl\{\nu : \exists\,\nu'\in\mathcal F \text{ with } \mathrm E(\nu')>\mu \text{ and } \mathrm{KL}(\nu,\nu')\le\gamma\bigr\}.$$
--   Then every $\nu\in\mathcal C_{\mu,\gamma}$ satisfies
--   $$\mathcal K_{\inf}(\nu,\mu)\le\gamma,$$
--   where $\mathcal K_{\inf}(\nu,\mu) = \inf\{\mathrm{KL}(\nu,\nu') : \nu'\in\mathcal F,\ \mathrm E(\nu')>\mu\}$.
--
--   The inclusion converts the event that the empirical distribution lies in $\mathcal C_{\mu,\gamma}$, on which the algorithm overestimates an arm, into a lower deviation of the empirical minimal divergence; this is the form in which the second sum of (10) is controlled.
--
--   **Formalization Note** The statement is for every measure $\nu$ on $\mathbb R$, not only for $\nu\in\mathfrak M_1([0,1])$; this is a stronger statement than the page's. $\mathcal K_{\inf}$ is valued in $[0,+\infty]$ and $\gamma$ is compared through its embedding.
-- source:
--   Cappé, Garivier, Maillard, Munos, Stoltz, Kullback–Leibler upper confidence bounds for optimal sequential allocation, arXiv:1210.1136v4, p. 9, (6) and (7), with 𝒟 = ℱ and Π_𝒟 = id of §5, p. 14

import Mathlib
import Definitions.Def_CappeKLUCB_Empirical_Setting

namespace CappeKLUCB.Empirical

open MeasureTheory ProbabilityTheory ImprovedLinBandits.UCBDelta RegretBandits.Stochastic
open scoped ENNReal

/-- Display (7), Cappé et al., arXiv:1210.1136v4, p. 9, with `𝒟 = ℱ` and `Π_𝒟` the identity
(§5, p. 14): `𝒞_{μ,γ} ⊆ {ν : 𝒦_inf(ν, μ) ≤ γ}`. -/
theorem inclusion_7 (μ γ : ℝ) (hγ : 0 < γ) (ν : Measure ℝ) (hν : InC μ γ ν) :
    Kinf ν μ ≤ ENNReal.ofReal γ := by sorry

end CappeKLUCB.Empirical
