-- Prove2me | Theorems.Thm_BauerleRiederMDP_Indifference_remark_4_9_3_price
-- name    : BauerleRiederMDP.Indifference.remark_4_9_3_price
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:29:09.453179+00:00
-- url     : https://prove2.me/theorems/36515337-cfa7-4f15-8d69-e517c53bbab4
-- title:
--   Remark 4.9.3 — the indifference price as a $\mathbb Q$-expectation
-- statement:
--   Let $s,\hat s>0$. The indifference price of Theorem 4.9.2 of a claim $H=h(S_1,\hat S_1)\ge 0$ can be written as
--   $$
--   v_0(H,s,\hat s)=\frac1\gamma\,\mathbb E_{\mathbb Q}\Bigl[\log\mathbb E_{\mathbb Q}\bigl[e^{\gamma H}\mid S_1\bigr]\ \Big|\ S_0=s,\hat S_0=\hat s\Bigr].
--   $$
--   If the payoff depends only on the traded asset, $H=h(S_1)$, then
--   $$
--   v_0(H,s,\hat s)=\mathbb E_{\mathbb Q}[H\mid S_0=s],
--   $$
--   independent of $\hat s$. Each formula is stated as the unique solution of the defining equation of Definition 4.9.1.
--
--   So indifference pricing agrees with arbitrage-free pricing for claims on the traded asset, and for general claims is a nonlinear expectation under $\mathbb Q$.
--
--   **Formalization Note** Conditioning on $S_0=s,\hat S_0=\hat s$ means working with $S_1=s\tilde R$ and $\hat S_1=\hat s\hat R$. The indifference price is the one of the published one-period market.
--
--   Differences from the source:
--   - reading: v₀(H, s, ŝ) = … as an equation for the price of Definition 4.9.1 → a number w satisfies the defining equation if and only if it equals the formula; reason: this states both that the formula is the price and that the price is well defined
--   - encoding: H a non-negative random variable with H = h(S₁, Ŝ₁) → h a function on ℝ² with h(sR̃(ω), ŝR̂(ω)) ≥ 0 for every ω; reason: on the four-point Ω every function of (S₁, Ŝ₁) is a random variable, and H ≥ 0 is exactly non-negativity at the four points
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Remark 4.9.3, p.137

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_Q
import Definitions.Def_BauerleRiederMDP_Indifference_Market_toOnePeriod

open MeasureTheory

namespace BauerleRiederMDP.Indifference

/-- Remark 4.9.3, price formulas (Bäuerle & Rieder, Markov Decision Processes with Applications to
Finance (2011), Remark 4.9.3, p.137, PDF 151). The indifference price of Theorem 4.9.2 can be written
as `v₀(H, s, ŝ) = (1/γ) 𝔼_ℚ[log 𝔼_ℚ[e^{γH} | S₁] | S₀ = s, Ŝ₀ = ŝ]`, and for a claim `H = h(S₁)` on the
traded asset only, `v₀(H, s, ŝ) = 𝔼_ℚ[H | S₀ = s]`, independent of `ŝ`.

**Formalization Note.** Conditioning on `S₀ = s, Ŝ₀ = ŝ` means taking `S₁ = s R̃`, `Ŝ₁ = ŝ R̂`. The
indifference price is that of Definition 4.9.1, the platform's
`OnePeriodIndifferenceMarket.IsIndifferencePrice`, and each formula is stated as the only solution
of its defining equation. `H ≥ 0` is the book's non-negative random variable: `h ≥ 0` at the
four points `(s R̃(ω), ŝ R̂(ω))`. -/
theorem remark_4_9_3_price (M : Market) (s ŝ : ℝ) (hs : 0 < s) (hŝ : 0 < ŝ) :
    (∀ h : ℝ → ℝ → ℝ, (∀ ω, 0 ≤ h (s * M.Rt ω) (ŝ * M.Rh ω)) → ∀ w : ℝ,
      M.toOnePeriod.IsIndifferencePrice h s ŝ w ↔
        w = 1 / M.γ * ∫ ω, Real.log
          ((M.Q[fun ω' => Real.exp (M.γ * h (s * M.Rt ω') (ŝ * M.Rh ω')) |
            MeasurableSpace.comap (fun ω' => s * M.Rt ω') inferInstance]) ω) ∂M.Q) ∧
    (∀ k : ℝ → ℝ, (∀ ω, 0 ≤ k (s * M.Rt ω)) → ∀ w : ℝ,
      M.toOnePeriod.IsIndifferencePrice (fun s₁ _ => k s₁) s ŝ w ↔
        w = ∫ ω, k (s * M.Rt ω) ∂M.Q) := by sorry

end BauerleRiederMDP.Indifference
