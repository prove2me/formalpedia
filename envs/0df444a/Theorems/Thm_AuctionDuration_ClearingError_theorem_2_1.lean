-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_theorem_2_1
-- name    : AuctionDuration.ClearingError.theorem_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:48:59.057391+00:00
-- url     : https://prove2.me/theorems/6dc628e6-f8c2-4fa3-a714-7a02747500a9
-- title:
--   Theorem 2.1, p. 10 — semi-explicit formula for the clearing-price error E(h) and the mid-price error E^mid(h)
-- statement:
--   Consider the first auction of the call-auction market: a Brownian efficient price $P_t=P_0+\sigma_fW_t$, market makers arriving as a Poisson process $N^{mm}$ of intensity $\mu$, an independent $\mathrm{Exp}(\nu)$ opening time $\tau^{op}_1$, clearing at $\tau^{cl}_1=\tau^{op}_1+h$ with $h\ge0$, i.i.d. centred estimation noises of variance $\sigma^2$, supply slope $K>0$, and a square-integrable market-taker imbalance $I_{\tau^{cl}_1}$. Let $E(h)$ and $E^{mid}(h)$ be the mean squared errors of the clearing price (2) and of the mid-price (3) with respect to the efficient price at the clearing, conditionally on at least one market maker being present. Write
--   $$c(h)=\Big(1-e^{-\mu h}\frac{\nu}{\nu+\mu}\Big)^{-1}e^{\nu h}.$$
--   Then both squared errors are integrable, and
--   $$E^{mid}(h)=c(h)\int_h^{+\infty}\nu e^{-\nu t}\Big(\Big(\sigma_f^2\frac t6+\sigma^2\Big)e^{-\mu t}\int_0^{\mu t}\frac{e^s-1}{s}\,ds+\sigma_f^2\frac t3\big(1-e^{-\mu t}\big)\Big)dt,$$
--   $$E(h)=E^{mid}(h)+\frac{\mathbb E[I^2_{\tau^{cl}_1}]}{K^2}\,c(h)\int_h^{+\infty}\nu e^{-\nu t}e^{-\mu t}\int_0^{\mu t}\frac1s\int_0^s\frac{e^u-1}{u}\,du\,ds\,dt .$$
--
--   The formula makes the trade-off in the auction duration $h$ explicit: a longer auction gathers more market makers but lets the efficient price move further from the views they sent. By Lemma 2.1 of the paper, $E(h)$ is the almost-sure long-run average squared error of the clearing prices, so a minimizer of this formula is an optimal auction duration.
--
--   **Formalization Note** $E$ and $E^{mid}$ are conditional expectations given $\tilde\Omega=\{N^{mm}_{\tau^{cl}_1}>0\}$, as in Appendix A; the model conditions the Poisson process and the opening time jointly on $\tilde\Omega$ (the reading of Assumption 2 used by the proof; the literal reading of p. 8 gives a different value, see the model's note). Added hypotheses: centred noises, independence of $I_{\tau^{cl}_1}$ from everything else, and continuous Brownian paths. $\mathbb E[I^2_{\tau^{cl}_1}]$ is taken under $\mathbb P$; it is the same under $\mathbb P(\cdot\mid\tilde\Omega)$ by independence. Inner integrands are $0$ at $s=0$ and $u=0$ in Lean, a null set.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, p. 10, Theorem 2.1 and (5)

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model

namespace AuctionDuration.ClearingError
open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

/-- Theorem 2.1, p. 10, with (5): the semi-explicit formulas for E(h) and E^mid(h). -/
theorem theorem_2_1 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (h : ℝ) (hh : 0 ≤ h) :
    let c : ℝ := (1 - Real.exp (-(p.mu * h)) * (p.nu / (p.nu + p.mu)))⁻¹ * Real.exp (p.nu * h)
    Integrable (fun ω => (Pcl p X h ω - Peff p X (tauCl X h ω) ω) ^ 2) (P[|OmegaT X h]) ∧
    Integrable (fun ω => (Pmid p X h ω - Peff p X (tauCl X h ω) ω) ^ 2) (P[|OmegaT X h]) ∧
    Emid p P X h = c * ∫ t in Set.Ioi h, p.nu * Real.exp (-(p.nu * t)) *
        ((p.sigmaF ^ 2 * (t / 6) + p.sigma ^ 2) * Real.exp (-(p.mu * t)) *
            (∫ s in (0 : ℝ)..(p.mu * t), (Real.exp s - 1) / s) +
          p.sigmaF ^ 2 * (t / 3) * (1 - Real.exp (-(p.mu * t)))) ∧
    E p P X h = Emid p P X h + (∫ ω, X.J ω ^ 2 ∂P) / p.K ^ 2 * c *
        ∫ t in Set.Ioi h, p.nu * Real.exp (-(p.nu * t)) * Real.exp (-(p.mu * t)) *
          ∫ s in (0 : ℝ)..(p.mu * t), (1 / s) * ∫ u in (0 : ℝ)..s, (Real.exp u - 1) / u := by sorry

end AuctionDuration.ClearingError
