-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_eq_9
-- name    : AuctionDuration.ClearingError.eq_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:08.318855+00:00
-- url     : https://prove2.me/theorems/c8a91363-3356-4986-ad6c-4924d40423be
-- title:
--   Appendix A, p. 20, (9) — probability that a market maker is present at the clearing
-- statement:
--   In the one-auction model, let $N^{mm}$ be the Poisson($\mu$) market-maker counting process, $\tau^{op}_1\sim\mathrm{Exp}(\nu)$ the independent opening time, and $\tau^{cl}_1=\tau^{op}_1+h$ the clearing time, with $\nu,\mu>0$ and $h\ge0$. Then the probability that at least one market maker is present at the clearing is
--   $$\mathbb P\big(N^{mm}_{\tau^{cl}_1}>0\big)=1-e^{-\mu h}\,\frac{\nu}{\nu+\mu}.$$
--
--   This is the normalizing constant of the conditional expectations $E(h)$ and $E^{mid}(h)$, and the factor $(1-e^{-\mu h}\nu/(\nu+\mu))^{-1}$ of Theorem 2.1.
--
--   **Formalization Note** The probability is the unconditional measure of $\tilde\Omega$, converted to a real number.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, p. 20, Appendix A, (9)

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model

namespace AuctionDuration.ClearingError
open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

/-- Appendix A, p. 20, (9): P(N^mm_{τ^cl_1} > 0) = 1 − e^{−µh} ν/(ν+µ). -/
theorem eq_9 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (h : ℝ) (hh : 0 ≤ h) :
    (P (OmegaT X h)).toReal = 1 - Real.exp (-(p.mu * h)) * (p.nu / (p.nu + p.mu)) := by sorry

end AuctionDuration.ClearingError
