-- Prove2me | Theorems.Thm_ErgSingMFG_Abelian_lemma_5_1
-- name    : ErgSingMFG.Abelian.lemma_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-23T03:56:10.283629+00:00
-- url     : https://prove2.me/theorems/3bcc7422-3b05-42fa-8909-10790b1c53ee
-- title:
--   Lemma 5.1, p. 10 — the map Φ = (K̂, Ĝ) of (5.1) is continuous on ℝ²₊ × (−c, 1)
-- statement:
--   Throughout, $\mathbb R_+=(0,\infty)$. The model data are the drift $b$ and volatility $\sigma$ of the state equation $dX^\nu_t=b(X^\nu_t)\,dt+\sigma(X^\nu_t)\,dB_t+d\nu_t$, $X_{0-}=x$ (2.1), the running profit $\pi(x,\theta)\ge0$, and the weights $F,f$ of the mean $\theta(\mu)=F\big(\int_{\mathbb R_+}f\,d\mu\big)$ (3.4). $S'$, $m'$ are the scale and speed densities of $X$, $\widehat S'$, $\widehat m'$ those of the diffusion $\widehat X$ with drift $b+\sigma\sigma'$, and $\widehat\varphi_r$ is the decreasing fundamental solution of $\mathcal L_{\widehat X}u-(r-b')u=0$ (2.10).
--
--   Assume Assumptions 2.1, 2.2, 3.3, 4.3 (with constant $c$) and the boundary requirements of §2.1, and let $r\mapsto\widehat\varphi_r$, $r\in(-c,1)$, be any family of decreasing fundamental solutions of (2.10). Then for all $x,\theta>0$ and $r\in(-c,1)$ the integrands of
--   $$\widehat K(x,\theta;r)=\int_x^\infty\frac{\widehat\varphi_r(y)}{\widehat\varphi_r(x)}\widehat m'(y)\big(\pi_x(y,\theta)-(r-b'(y))\big)dy,\qquad\widehat G(x,\theta)=\int_x^\infty\big(f(y)-F^{-1}(\theta)\big)m'(y)\,dy$$
--   are integrable, and the map
--   $$\Phi:\mathbb R_+^2\times(-c,1)\to\mathbb R^2,\qquad\Phi(x,\theta;r)=\big(\widehat K(x,\theta;r),\widehat G(x,\theta)\big)\qquad(5.1)$$
--   is continuous.
--
--   The zeros of $\Phi(\cdot,\cdot;r)$ are the discounted equilibria ($r>0$) and the ergodic equilibrium ($r=0$), so this continuity is the first ingredient of the Abelian limit.
--
--   Differences from the source:
--   - reading: F⁻¹(θ) for every θ > 0 in Ĝ, Q and Φ → F⁻¹ on [F(0), ∞), extended by 0 on (0, F(0)] (`Finv`); reason: F⁻¹ is undefined below F(0) when F(0) > 0; the extension is continuous, it is the paper’s function when F(0) = 0 (Remark 3.4), and neither f(x⋆(θ)) = F⁻¹(θ) nor Q(θ) = 0 has a root in (0, F(0)] under it (paper.md slip 3)
--   - encoding: Φ built from the fundamental solutions φ̂_r, normalized in the proof by φ̂_r(a) = 1 → Φ built from an arbitrary family r ↦ φ̂_r of decreasing fundamental solutions; reason: K̂(x, θ; r) is invariant under rescaling φ̂_r for each r, so the map Φ does not depend on the family
--   - encoding: the integrals K(x, θ), Ĝ(x, θ), Q(θ) taken as finite numbers → Bochner integrals over (x, ∞) together with an explicit integrability clause; reason: a Bochner integral of a non-integrable function is 0 in Lean; the clause excludes that junk value
--   - encoding: the fundamental solution φ̂_r of (2.10), defined up to a positive factor → every positive C² solution of (2.10) on ℝ₊ tending to 0 at +∞ (`IsDecrFundHat`), quantified universally; reason: under natural boundaries these are exactly the positive multiples of φ̂_r, and the statement is invariant under positive rescaling
--   - generalization: Assumption 3.3(i): F, f continuously differentiable on [0, ∞) with F′, f′ > 0 → F, f continuous on [0, ∞), C¹ on (0, ∞) with F′, f′ > 0 there; reason: the paper’s own benchmark f(x) = x^β, F(y) = y^{1/β} (Remark 3.4, §7) fails the printed condition at 0; the proofs use F′ only at F⁻¹(θ) > 0; every model satisfying the printed condition satisfies this one
--   - encoding: arbitrary base point x_o ∈ ℝ₊ in S′ and Ŝ′ → x_o = 1; reason: changing x_o multiplies S′, Ŝ′, m′, m̂′ by positive constants, and every equation and assumption used is invariant under this
--   - encoding: “0 and +∞ are natural boundaries for X and X̂” (p. 6) → Feller’s four integral tests for the scale and speed densities of each process (`NaturalBdry`, inside `FundReq`); reason: Feller’s classification is the definition of a natural boundary; the listed properties (2.11)–(2.14) are its consequences
-- source:
--   Cao, Dianetti, Ferrari, Stationary Discounted and Ergodic Mean Field Games with Singular Controls, arXiv:2105.07213v1, p. 10, Lemma 5.1; proof pp. 22–23 (Appendix 9.3)

import Mathlib
import Definitions.Def_ErgSingMFG_Abelian_Analytic
import Definitions.Def_ErgSingMFG_Abelian_Systems

open Set Filter MeasureTheory
open scoped Topology

namespace ErgSingMFG.Abelian

/-- Lemma 5.1 (p. 10): the map `Φ(x, θ; r) = (K̂(x, θ; r), Ĝ(x, θ))` of (5.1) is well defined (both
integrands are integrable on `(x, ∞)`) and continuous on `ℝ₊² × (−c, 1)`, for every family
`r ↦ φ̂_r` of decreasing fundamental solutions of (2.10). -/
theorem lemma_5_1 (m : Model)
    (h21 : Asm21 m) (h22 : Asm22 m) (h33 : Asm33 m) (hFR : FundReq m) (h43 : Asm43 m)
    (φh : ℝ → ℝ → ℝ) (hφ : ∀ r ∈ Ioo (-m.c) 1, IsDecrFundHat m r (φh r)) :
    (∀ x > 0, ∀ θ > 0, ∀ r ∈ Ioo (-m.c) 1,
      IntegrableOn (fun y => φh r y * Pi m y θ r) (Ioi x) ∧
      IntegrableOn (fun y => (m.f y - Finv m θ) * mp m y) (Ioi x)) ∧
    ContinuousOn (fun p : ℝ × ℝ × ℝ => Phi m φh p.1 p.2.1 p.2.2)
      (Ioi 0 ×ˢ Ioi 0 ×ˢ Ioo (-m.c) 1) := by sorry

end ErgSingMFG.Abelian
