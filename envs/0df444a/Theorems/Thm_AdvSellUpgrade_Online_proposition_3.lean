-- Prove2me | Theorems.Thm_AdvSellUpgrade_Online_proposition_3
-- name    : AdvSellUpgrade.Online.proposition_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:51:31.598986+00:00
-- url     : https://prove2.me/theorems/7684cedb-c92e-4a6d-b9b7-9c33ac98901d
-- title:
--   Proposition 3, p. 15 — under S with a deterministic rate λ, the optimal price is Bₛ + p(λ), the cutoff c(λ), the revenue π(λ) + Bₛ
-- statement:
--   Let $0<\lambda<\mu$, $\bar c>0$ and $B_s\in\mathbb R$. Under the spot-only scheme S with deterministic arrival rate $\lambda$, a fast-track price $P_s\ge B_s$ induces the equilibrium cutoff $c^e(P_s-B_s)$ of (5) and the revenue per customer
--   $$\Pi^{S}(P_s)=(P_s-B_s)\Bigl(1-\frac{c^e(P_s-B_s)}{\bar c}\Bigr)+B_s .$$
--   Then
--   $$\max_{P_s\ge B_s}\Pi^{S}(P_s)=\pi(\lambda)+B_s,$$
--   the maximum is attained exactly at $P_s^\star=B_s+p(\lambda)$, and the optimal cutoff is $c^e(p(\lambda))=c(\lambda)$.
--
--   Applied to $\lambda=\lambda_h$ and $\lambda=\lambda_l$, this gives the state-dependent priority-pricing benchmark $\alpha\pi(\lambda_h)+(1-\alpha)\pi(\lambda_l)+B_s$ against which the advance-selling schemes are compared.
--
--   **Formalization Note** The paper states the result for $\lambda_i$, $i\in\{h,l\}$ (the cases $\alpha=1$ and $\alpha=0$ of (6)); it is stated here for every rate $\lambda\in(0,\mu)$. "The optimal price is" is formalized as uniqueness of the maximiser among $P_s\ge B_s$.
-- source:
--   Wang, Cao, Xie, Zhan, Advance Selling and Upgrading in Priority Queues, MSOM (2025), doi:10.1287/msom.2023.0410, p. 15, Proposition 3; p. 14, (5)–(6)

import Mathlib
import Definitions.Def_AdvSellUpgrade_Online_Setting

namespace AdvSellUpgrade.Online

/-- Proposition 3, p. 15: under the spot-only scheme S with a deterministic rate `λ ∈ (0, µ)`, the
revenue `Π^S(Ps)` over `Ps ≥ Bs` has maximum `π(λ) + Bs`, attained at the price `Bs + p(λ)` only,
whose equilibrium cutoff is `c(λ)`. -/
theorem proposition_3 (mu cbar lam Bs : ℝ) (hlam : 0 < lam) (hlammu : lam < mu)
    (hcbar : 0 < cbar) :
    IsGreatest (revS mu cbar lam Bs '' Set.Ici Bs) (piFn mu cbar lam + Bs) ∧
      revS mu cbar lam Bs (Bs + pFn mu cbar lam) = piFn mu cbar lam + Bs ∧
      cS mu cbar lam (pFn mu cbar lam) = cFn mu cbar lam ∧
      (∀ Ps, Bs ≤ Ps → revS mu cbar lam Bs Ps = piFn mu cbar lam + Bs →
        Ps = Bs + pFn mu cbar lam) := by sorry

end AdvSellUpgrade.Online
