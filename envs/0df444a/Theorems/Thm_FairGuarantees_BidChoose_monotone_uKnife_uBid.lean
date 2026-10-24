-- Prove2me | Theorems.Thm_FairGuarantees_BidChoose_monotone_uKnife_uBid
-- name    : FairGuarantees.BidChoose.monotone_uKnife_uBid
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:42.778651+00:00
-- url     : https://prove2.me/theorems/7c47963e-bba5-48c8-8528-f0b207897015
-- title:
--   §5.2, p. 19 — u^κ and u^θ decrease weakly in t¹ and increase weakly in t²
-- statement:
--   Let $\Omega\subseteq\mathbb R^d$ ($d\ge1$) be a manna, $u\in\mathcal D(\Omega)\cap\mathcal M^+(\Omega)$ an increasing utility, $\kappa$ a moving knife and $\theta$ a benchmark measure. On the triangle $\mathcal T=\{(t^1,t^2):0\le t^1\le t^2\le1\}$, both the knife utility $u^\kappa$ and the indirect utility $u^\theta$ of (5) are weakly decreasing in $t^1$ and weakly increasing in $t^2$: for $0\le t^1\le t^{1\prime}\le t^2\le t^{2\prime}\le1$ and $\alpha\in\{\kappa,\theta\}$,
--   $$
--   u^\alpha(t^{1\prime},t^2)\le u^\alpha(t^1,t^2),\qquad u^\alpha(t^1,t^2)\le u^\alpha(t^1,t^{2\prime}).
--   $$
--
--   These monotonicity properties drive the optimality argument for the equalising sequences of Lemma 4 ii).
--
--   **Formalization Note.** Each inequality is stated with all its points on the triangle. The dimension is assumed positive, as in every theorem of this mission: in $\mathbb R^0$ Lebesgue measure is a unit point mass, which the paper's non-atomic model (§3, "Non atomic fair division") excludes.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 19, §5.2, first line

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory

namespace FairGuarantees.BidChoose

/-- §5.2, p. 19, first line: on the triangle `0 ≤ t¹ ≤ t² ≤ 1`, both `u^κ` and `u^θ` are
weakly decreasing in `t¹` and weakly increasing in `t²`. -/
theorem monotone_uKnife_uBid {d : ℕ} (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {K : ℝ → Set (FairGuarantees.DivideChoose.E d)} (hK : IsKnife Ω K) {θ : Measure (FairGuarantees.DivideChoose.E d)} (hθ : IsBenchmark Ω θ) :
    (∀ t₁ t₁' t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₁' → t₁' ≤ t₂ → t₂ ≤ 1 →
        uKnife u K t₁' t₂ ≤ uKnife u K t₁ t₂) ∧
    (∀ t₁ t₂ t₂' : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₂' → t₂' ≤ 1 →
        uKnife u K t₁ t₂ ≤ uKnife u K t₁ t₂') ∧
    (∀ t₁ t₁' t₂ : ℝ, 0 ≤ t₁ → t₁ ≤ t₁' → t₁' ≤ t₂ → t₂ ≤ 1 →
        uBid Ω θ u t₁' t₂ ≤ uBid Ω θ u t₁ t₂) ∧
    (∀ t₁ t₂ t₂' : ℝ, 0 ≤ t₁ → t₁ ≤ t₂ → t₂ ≤ t₂' → t₂' ≤ 1 →
        uBid Ω θ u t₁ t₂ ≤ uBid Ω θ u t₁ t₂') := by sorry

end FairGuarantees.BidChoose
