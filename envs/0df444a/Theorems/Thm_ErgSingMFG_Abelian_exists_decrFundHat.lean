-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_exists_decrFundHat
-- name    : ErgSingMFG.Abelian.exists_decrFundHat
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-29T18:51:40.559163+00:00
-- url     : https://prove2.me/theorems/5e6fe2c6-5fd6-4446-8187-1e5b4ae9e3f5
-- title:
--   §2.1, p. 6, (2.10) — existence of the decreasing fundamental solution $\widehat\varphi_r$ when $r-b'\ge r_0>0$
-- statement:
--   Let $b,\sigma$ be the drift and volatility of the model, satisfying Assumption 2.1 ($b,\sigma\in C^1(\mathbb R_+)$, $\sigma>0$, $b,\sigma$ globally Lipschitz, $\sigma\sigma'$ locally Lipschitz), and suppose the boundary requirements of §2.1 hold (in particular $0$ and $+\infty$ are natural boundaries, in Feller's sense, for the diffusion $\widehat X$ with drift $b+\sigma\sigma'$ and volatility $\sigma$; this is the hypothesis `FundReq`).
--
--   Let $r\in\mathbb R$ and suppose the killing rate is bounded away from zero: there is $r_0>0$ with
--   $$r-b'(x)\ \ge\ r_0\qquad\text{for all }x>0 .$$
--   Then the ODE (2.10)
--   $$\mathcal L_{\widehat X}u(x)-(r-b'(x))\,u(x)=0,\qquad \mathcal L_{\widehat X}u=\tfrac12\sigma^2u''+(b+\sigma\sigma')u',\qquad x\in\mathbb R_+,$$
--   admits a decreasing fundamental solution $\widehat\varphi_r$: a function that is $C^2$ and strictly positive on $(0,\infty)$, solves (2.10) on $(0,\infty)$, and satisfies $\widehat\varphi_r(x)\to0$ as $x\to\infty$ (`IsDecrFundHat m r φ`).
--
--   This is the existence statement the paper takes for granted on p. 6 ("when $r-b'(x)\ge r_o>0$ for $x\in\mathbb R_+$, any solution to the ODE (2.10) can be written as a linear combination of the fundamental solutions $\widehat\psi_r$ and $\widehat\varphi_r$"), with reference to Borodin and Salminen (2015), Chapter II. In §5 the paper uses $\widehat\varphi_r$ for every $r\in(-c,1)$, where Assumption 4.3 ($b'<-2c$) gives $r-b'>r+2c>c>0$; it enters the map $\Phi$ of (5.1), Lemma 5.1 and the proof of Theorem 5.2.
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, §2.1, p. 6, ODE (2.10) and the sentence preceding it (fundamental solutions ψ̂_r, φ̂_r when r − b′ ≥ r_o > 0); used for r ∈ (−c, 1) in §5 (5.1) and Appendix 9.3–9.4; cf. Borodin–Salminen (2015), Ch. II.

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic

open Set Filter MeasureTheory
open scoped Topology

namespace ErgSingMFG.Abelian

/-- §2.1 (p. 6), around (2.10): when `r − b′(x) ≥ r₀ > 0` on `ℝ₊`, the ODE
`𝓛_X̂ u − (r − b′)u = 0` has a decreasing fundamental solution `φ̂_r`: a positive `C²` solution
on `(0, ∞)` that vanishes at `+∞` (the boundary `+∞` of `X̂` being natural). -/
theorem exists_decrFundHat (m : Model) (h21 : Asm21 m) (hFR : FundReq m) (r r₀ : ℝ)
    (hr₀ : 0 < r₀) (hk : ∀ x > 0, r₀ ≤ r - deriv m.b x) :
    ∃ φ : ℝ → ℝ, IsDecrFundHat m r φ := by sorry

end ErgSingMFG.Abelian
