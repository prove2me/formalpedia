-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_eq_8
-- name    : AuctionDuration.ClearingError.eq_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:00.275689+00:00
-- url     : https://prove2.me/theorems/b8a83efa-ccbf-42d4-9889-655316517af0
-- title:
--   Appendix A, p. 20, (8) — reduction of E(h) to the functions g, f, ℓ at deterministic times
-- statement:
--   In the one-auction model, write $N^{mm}$ for the market-maker counting process, $\tilde\Omega=\{N^{mm}_{\tau^{cl}_1}>0\}$, and, for a deterministic $t$,
--   $$g(t)=\mathbb E\Big[\mathbf 1_{N^{mm}_t>0}\Big(\sum_{k=1}^{N^{mm}_t}\frac{P_{\tau^{mm}_k}-P_t}{N^{mm}_t}\Big)^2\Big],\quad f(t)=\mathbb E\Big[\frac{\mathbf 1_{N^{mm}_t>0}}{N^{mm}_t}\Big],\quad \ell(t)=\mathbb E[I^2_{\tau^{cl}_1}]\,\mathbb E\Big[\frac{\mathbf 1_{N^{mm}_t>0}}{(N^{mm}_t)^2}\Big].$$
--   Then the squared clearing-price error is integrable under $\mathbb P(\cdot\mid\tilde\Omega)$, the integrand below is integrable on $(h,\infty)$, and
--   $$E(h)=\mathbb P\big(N^{mm}_{\tau^{cl}_1}>0\big)^{-1}e^{\nu h}\int_h^{+\infty}\nu e^{-\nu t}\Big(g(t)+\sigma^2 f(t)+\frac1{K^2}\ell(t)\Big)\,dt .$$
--
--   The identity separates the three sources of error of the clearing price (the price moves since the market makers' arrivals, their estimation noise, and the market takers' imbalance) and reduces the random clearing time to an integral over deterministic times.
--
--   **Formalization Note** The page displays a chain of three equalities; this item states its outer two sides. The integrability conjuncts rule out junk values of the Bochner integrals. The identity uses the added hypotheses $\mathbb E[g_k]=0$ and the independence of $I_{\tau^{cl}_1}$ (see the model's note).
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, p. 20, Appendix A, (8)

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model

namespace AuctionDuration.ClearingError
open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

/-- Appendix A, p. 20, (8): reduction of E(h) to the auxiliary functions g, f, ℓ at deterministic
times, E(h) = P(N^mm_{τ^cl_1} > 0)^{-1} e^{νh} ∫_h^∞ νe^{−νt} (g(t) + σ² f(t) + ℓ(t)/K²) dt. -/
theorem eq_8 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (h : ℝ) (hh : 0 ≤ h) :
    Integrable (fun ω => (Pcl p X h ω - Peff p X (tauCl X h ω) ω) ^ 2) (P[|OmegaT X h]) ∧
    IntegrableOn (fun t => p.nu * Real.exp (-(p.nu * t)) *
        (gFun p P X t + p.sigma ^ 2 * fFun P X t + ellFun P X t / p.K ^ 2)) (Set.Ioi h) ∧
    E p P X h = ((P (OmegaT X h)).toReal)⁻¹ * Real.exp (p.nu * h) *
      ∫ t in Set.Ioi h, p.nu * Real.exp (-(p.nu * t)) *
        (gFun p P X t + p.sigma ^ 2 * fFun P X t + ellFun P X t / p.K ^ 2) := by sorry

end AuctionDuration.ClearingError
