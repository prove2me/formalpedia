-- Prove2me | Theorems.Thm_FairGuarantees_BidChoose_right_hand_construction
-- name    : FairGuarantees.BidChoose.right_hand_construction
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:55.797168+00:00
-- url     : https://prove2.me/theorems/69dc825f-e742-4010-8bd7-baf2d335d4fe
-- title:
--   §5.2, p. 20, proof of Theorem 2 iii) for B&C^θ_n — min_k u^θ(t^k, t^{k+1}) ≤ Maxmin(u; n) for every τ ∈ Υ(n)
-- statement:
--   Let $n\ge1$, $\Omega\subseteq\mathbb R^d$ ($d\ge1$) a manna, $u\in\mathcal D(\Omega)\cap\mathcal M^+(\Omega)$ and $\theta$ a benchmark measure. For every $\tau=(t^k)_{0\le k\le n}\in\Upsilon(n)$,
--   $$
--   \min_{0\le k\le n-1}u^\theta(t^k,t^{k+1})\le \mathit{Maxmin}(u;n).
--   $$
--
--   Taking the supremum over $\tau$ gives $\Gamma^\theta(u;n)\le\mathit{Maxmin}(u;n)$, the right-hand inequality of Theorem 2 iii) for the Bid & Choose rule.
--
--   **Formalization Note.** The page builds a partition whose $k$-th share is worth at least $u^\theta(t^{k-1}_\theta,t^k_\theta)$ along the optimal sequence $t_\theta$; the construction works, up to an arbitrary $\varepsilon>0$, for every $\tau\in\Upsilon(n)$, which is the form stated here. It does not need $t_\theta$ to exist.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 20, §5.2, proof of Theorem 2, Statement iii) for B&C^θ_n, Right hand inequality

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory

namespace FairGuarantees.BidChoose

/-- §5.2, p. 20, proof of Theorem 2 iii) for B&C^θ_n, right-hand inequality, for an arbitrary
`τ ∈ Υ(n)`: `min_k u^θ(t^k, t^{k+1}) ≤ FairGuarantees.DivideChoose.Maxmin(u; n)`. -/
theorem right_hand_construction {d n : ℕ} [NeZero n] (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)}
    (hΩ : FairGuarantees.DivideChoose.IsManna Ω) {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {θ : Measure (FairGuarantees.DivideChoose.E d)} (hθ : IsBenchmark Ω θ) :
    ∀ τ : Fin (n + 1) → ℝ, IsUpsilon n τ →
      ⨅ k : Fin n, uBid Ω θ u (τ k.castSucc) (τ k.succ) ≤ FairGuarantees.DivideChoose.Maxmin Ω u n := by sorry

end FairGuarantees.BidChoose
