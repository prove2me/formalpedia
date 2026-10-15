-- Prove2me | Theorems.Thm_FairGuarantees_BidChoose_lemma_4_ii_knife
-- name    : FairGuarantees.BidChoose.lemma_4_ii_knife
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:55.211964+00:00
-- url     : https://prove2.me/theorems/803b013b-7ed9-4fb9-a147-782adc6c1e2e
-- title:
--   Lemma 4 ii), p. 19, κ part — Γ^κ(u; n) is attained at an equalising τ ∈ Υ(n)
-- statement:
--   Let $n\ge1$, $\Omega\subseteq\mathbb R^d$ ($d\ge1$) a manna, $u\in\mathcal D(\Omega)\cap\mathcal M^+(\Omega)$ and $\kappa$ a moving knife. There are a sequence $\tau=(t^k)_{0\le k\le n}\in\Upsilon(n)$ and a number $\lambda$ such that
--   $$
--   u^\kappa(t^k,t^{k+1})=\lambda\quad(0\le k\le n-1)\qquad\text{and}\qquad \lambda=\Gamma^\kappa(u;n).
--   $$
--   In particular the supremum in (6) for $\alpha=\kappa$ is a maximum, attained at a sequence equalising all the knife utilities.
--
--   This equalising sequence is the stopping schedule of the Moving Knife strategy in Theorem 2 i), and its knife pieces form an equipartition whose value is $\Gamma^\kappa(u;n)$.
--
--   **Formalization Note.** Only the $\kappa$ part of Lemma 4 ii) is stated: for $\theta$ an equalising sequence need not exist (a counterexample in $\mathcal M^+([0,1])$ with $n=2$ is recorded with the mission). "The sequence $t^k$ increases in $k$" is the monotonicity already built into $\Upsilon(n)$.
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 19, Lemma 4 ii) (κ part); proof in the Appendix, p. 25

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory

namespace FairGuarantees.BidChoose

/-- Lemma 4 ii), p. 19, the κ part: the maximum in (6) for `u^κ` is achieved at some
`τ ∈ Υ(n)` at which all the terms `u^κ(t^k, t^{k+1})` are equal, and their common value is
`Γ^κ(u; n)`. -/
theorem lemma_4_ii_knife {d n : ℕ} [NeZero n] (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)} (hΩ : FairGuarantees.DivideChoose.IsManna Ω)
    {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {K : ℝ → Set (FairGuarantees.DivideChoose.E d)} (hK : IsKnife Ω K) :
    ∃ τ : Fin (n + 1) → ℝ, IsUpsilon n τ ∧ ∃ c : ℝ,
      (∀ k : Fin n, uKnife u K (τ k.castSucc) (τ k.succ) = c) ∧
      c = Gamma n (uKnife u K) := by sorry

end FairGuarantees.BidChoose
