-- Prove2me | Theorems.Thm_FairGuarantees_BidChoose_knife_equipartition
-- name    : FairGuarantees.BidChoose.knife_equipartition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T08:59:50.410545+00:00
-- url     : https://prove2.me/theorems/933b68f9-92f4-4248-b0dc-da3bb5d44807
-- title:
--   §5.2, p. 19, proof of Theorem 2 — an equalising knife sequence yields an n-equipartition of Ω
-- statement:
--   Let $n\ge1$, $\Omega\subseteq\mathbb R^d$ ($d\ge1$) a manna, $u\in\mathcal D(\Omega)\cap\mathcal M^+(\Omega)$ and $\kappa$ a moving knife. If $\tau=(t^k)\in\Upsilon(n)$ and $\lambda\in\mathbb R$ satisfy $u^\kappa(t^k,t^{k+1})=\lambda$ for $0\le k\le n-1$, then the knife pieces
--   $$
--   \Pi=\big(K(t^{k+1})\setminus K(t^k)\big)_{0\le k\le n-1}
--   $$
--   form an $n$-equipartition of $\Omega$, $\Pi\in\mathcal{EP}_n(\Omega;u)$, and every piece has utility $\lambda$.
--
--   Combined with Lemma 4 ii) and Proposition 1 ii), this places $\Gamma^\kappa(u;n)$ between $\mathit{minMax}(u;n)$ and $\mathit{Maxmin}(u;n)$.
--
--   **Formalization Note.** Pieces are indexed $0,\dots,n-1$ (the paper's $k=1,\dots,n$ shifted by one).
-- source:
--   Bogomolnaia & Moulin, Guarantees in Fair Division, arXiv:1911.10009v3, p. 19, §5.2, proof of Theorem 2, Statement i) and iii) for MK^κ_n, first sentence

import Mathlib
import Definitions.Def_FairGuarantees_DivideChoose_Setting
import Definitions.Def_FairGuarantees_BidChoose_Guarantees

open MeasureTheory

namespace FairGuarantees.BidChoose

/-- §5.2, p. 19, proof of Theorem 2, first sentence: if `τ ∈ Υ(n)` equalises the knife
utilities at a common value `c`, the knife pieces `K(t^{k+1}) ∖ K(t^k)` form an
`n`-equipartition of `Ω` whose shares all have utility `c`. -/
theorem knife_equipartition {d n : ℕ} [NeZero n] (hd : 0 < d) {Ω : Set (FairGuarantees.DivideChoose.E d)}
    (hΩ : FairGuarantees.DivideChoose.IsManna Ω) {u : Set (FairGuarantees.DivideChoose.E d) → ℝ} (hu : FairGuarantees.DivideChoose.IsUtility Ω u) (hinc : FairGuarantees.DivideChoose.IsIncreasing Ω u)
    {K : ℝ → Set (FairGuarantees.DivideChoose.E d)} (hK : IsKnife Ω K) {τ : Fin (n + 1) → ℝ} (hτ : IsUpsilon n τ)
    {c : ℝ} (hc : ∀ k : Fin n, uKnife u K (τ k.castSucc) (τ k.succ) = c) :
    FairGuarantees.DivideChoose.IsEquipartition Ω u Ω n (fun k : Fin n => K (τ k.succ) \ K (τ k.castSucc)) ∧
      ∀ k : Fin n, u (K (τ k.succ) \ K (τ k.castSucc)) = c := by sorry

end FairGuarantees.BidChoose
