-- Prove2me | Theorems.Thm_FairGuarantees_BidChoose_theorem_2_iii
-- name    : FairGuarantees.BidChoose.theorem_2_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:55.412111+00:00
-- url     : https://prove2.me/theorems/e30c5068-980c-468d-a776-c37ff3d53efb
-- title:
--   Theorem 2 iii), p. 19 — for u ∈ M⁺(Ω): minMax ≤ Γ^κ ≤ Maxmin for every knife κ, and Γ^θ ≤ Maxmin for every measure θ
-- statement:
--   Let $n\ge1$ be the number of agents, $\Omega\subseteq\mathbb R^d$ ($d\ge1$) a manna, and $u\in\mathcal D(\Omega)\cap\mathcal M^+(\Omega)$ an increasing utility. Let $\kappa$ be a moving knife through $\Omega$ and $\theta$ a benchmark measure on $\Omega$, with the Moving Knife guarantee $\Gamma^\kappa(u;n)$ and the Bid & Choose guarantee $\Gamma^\theta(u;n)$ defined by (6). Then
--   $$
--   \mathit{minMax}(u;n)\le\Gamma^\kappa(u;n)\le\mathit{Maxmin}(u;n)
--   \qquad\text{and}\qquad
--   \Gamma^\theta(u;n)\le\mathit{Maxmin}(u;n).
--   $$
--
--   The Moving Knife guarantee therefore always improves, at least weakly, on the minMax guarantee of Divide & Choose and never exceeds the Maxmin upper bound on fair guarantees; the Bid & Choose guarantee never exceeds Maxmin either.
--
--   **Formalization Note.** The paper states $\mathit{minMax}(u;n)\le\Gamma^\alpha(u;n)\le\mathit{Maxmin}(u;n)$ for $\alpha=\kappa$ and $\alpha=\theta$. The inequality $\mathit{minMax}(u;n)\le\Gamma^\theta(u;n)$ is omitted because it is false: with $\Omega=[0,1]$, $\theta$ Lebesgue measure and $n=2$, there is a $u\in\mathcal M^+(\Omega)$ for which every share of measure at most $1/4$ and some share of every measure below $3/4$ are worth almost nothing, so $\Gamma^\theta(u;2)\le0.075$, while every 2-partition has a share worth about $0.9$. The dimension is assumed positive (Lebesgue measure on $\mathbb R^0$ is a point mass, excluded by the paper's non-atomic model).
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 19, Theorem 2 iii) (α = κ in full; α = θ right-hand inequality)

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory

namespace FairGuarantees.BidChoose

/-- Theorem 2 iii), p. 19, for `u ∈ M⁺(Ω)`: `minMax(u; n) ≤ Γ^κ(u; n) ≤ FairGuarantees.DivideChoose.Maxmin(u; n)` for every
moving knife `κ`, and `Γ^θ(u; n) ≤ FairGuarantees.DivideChoose.Maxmin(u; n)` for every benchmark measure `θ`. The page's
fourth inequality `minMax(u; n) ≤ Γ^θ(u; n)` is false in general and is not stated. -/
theorem theorem_2_iii {d n : ℕ} [NeZero n] (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {K : ℝ → Set (FairGuarantees.DivideChoose.E d)} (hK : IsKnife Ω K) {θ : Measure (FairGuarantees.DivideChoose.E d)} (hθ : IsBenchmark Ω θ) :
    FairGuarantees.DivideChoose.minMax Ω u n ≤ Gamma n (uKnife u K) ∧ Gamma n (uKnife u K) ≤ FairGuarantees.DivideChoose.Maxmin Ω u n ∧
      Gamma n (uBid Ω θ u) ≤ FairGuarantees.DivideChoose.Maxmin Ω u n := by sorry

end FairGuarantees.BidChoose
