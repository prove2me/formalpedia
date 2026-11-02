-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_eq_8_mid
-- name    : AuctionDuration.ClearingError.eq_8_mid
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-11-01T19:20:15.397948+00:00
-- url     : https://prove2.me/theorems/a56ad13a-e1a4-4037-973b-255063e7a936
-- title:
--   Appendix A, (8) for the mid-price — E^mid(h) = P(N^{mm}_{τ^{cl}_1} > 0)^{−1} e^{νh} ∫_h^∞ νe^{−νt}(g(t) + σ²f(t)) dt
-- statement:
--   This is the mid-price counterpart of equation (8) in Appendix A of Jusselin, Mastrolia and Rosenbaum: it reduces the conditional mean squared error of the mid-price at the first clearing to expectations at deterministic times.
--
--   Consider the first call auction of the model: efficient price $P_t=P_0+\sigma_f W_t$, market makers arriving as a Poisson process $N^{mm}$ of intensity $\mu$ (arrival times $\tau^{mm}_k$), an independent $\mathrm{Exp}(\nu)$ opening time $\tau^{op}_1$, clearing time $\tau^{cl}_1=\tau^{op}_1+h$ with $h\ge 0$, and i.i.d. centred estimation noises $g_k$ of variance $\sigma^2$. Let $\tilde\Omega=\{N^{mm}_{\tau^{cl}_1}>0\}$ and let
--   $$E^{mid}(h)=\mathbb E\big[(P^{mid}_{\tau^{cl}_1}-P_{\tau^{cl}_1})^2\,\big|\,\tilde\Omega\big],\qquad P^{mid}_{\tau^{cl}_1}=\frac{1}{N^{mm}_{\tau^{cl}_1}}\sum_{k=1}^{N^{mm}_{\tau^{cl}_1}}\big(P_{\tau^{mm}_k}+g_k\big).$$
--   With the deterministic-time functions
--   $$g(t)=\mathbb E\Big[\mathbf 1_{N^{mm}_t>0}\Big(\sum_{k=1}^{N^{mm}_t}\frac{P_{\tau^{mm}_k}-P_t}{N^{mm}_t}\Big)^2\Big],\qquad f(t)=\mathbb E\Big[\frac{\mathbf 1_{N^{mm}_t>0}}{N^{mm}_t}\Big],$$
--   the squared mid-price error is integrable under $\mathbb P(\cdot\mid\tilde\Omega)$, the function $t\mapsto \nu e^{-\nu t}(g(t)+\sigma^2 f(t))$ is integrable on $(h,\infty)$, and
--   $$E^{mid}(h)=\mathbb P\big(N^{mm}_{\tau^{cl}_1}>0\big)^{-1}e^{\nu h}\int_h^{+\infty}\nu e^{-\nu t}\big(g(t)+\sigma^2 f(t)\big)\,dt .$$
--
--   This is the computation (8) of Appendix A with the market-taker term $\ell(t)/K^2$ removed: the clearing price (2) is the mid-price (3) plus $I_{\tau^{cl}_1}/(KN^{mm}_{\tau^{cl}_1})$, and Theorem 2.1 states the resulting formula (5) for $E^{mid}(h)$ alongside the one for $E(h)$. Together with (9), Lemma A.1 and Lemma A.2 it yields the explicit formula for $E^{mid}(h)$.
--
--   **Formalization Note** The model is the platform definition `AuctionDuration_ClearingError_Model` used by the mission's other statements (`eq_8` is the same statement for $E(h)$); conditioning on $\tilde\Omega$ is `P[|OmegaT X h]`.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, Appendix A (proof of Theorem 2.1), p. 20, eq. (8) with the ℓ term removed, giving E^mid of Theorem 2.1, p. 10, eq. (5)

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model

namespace AuctionDuration.ClearingError
open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

/-- Appendix A, p. 20, (8) for the mid-price: E^mid(h) =
P(N^mm_{τ^cl_1} > 0)^{-1} e^{νh} ∫_h^∞ νe^{−νt} (g(t) + σ² f(t)) dt. -/
theorem eq_8_mid {Ω : Type*} [MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (h : ℝ) (hh : 0 ≤ h) :
    Integrable (fun ω => (Pmid p X h ω - Peff p X (tauCl X h ω) ω) ^ 2) (P[|OmegaT X h]) ∧
    IntegrableOn (fun t => p.nu * Real.exp (-(p.nu * t)) *
        (gFun p P X t + p.sigma ^ 2 * fFun P X t)) (Set.Ioi h) ∧
    Emid p P X h = ((P (OmegaT X h)).toReal)⁻¹ * Real.exp (p.nu * h) *
      ∫ t in Set.Ioi h, p.nu * Real.exp (-(p.nu * t)) *
        (gFun p P X t + p.sigma ^ 2 * fFun P X t) := by sorry

end AuctionDuration.ClearingError
