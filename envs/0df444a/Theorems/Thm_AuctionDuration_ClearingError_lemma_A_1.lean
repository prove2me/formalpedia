-- Prove2me | Theorems.Thm_AuctionDuration_ClearingError_lemma_A_1
-- name    : AuctionDuration.ClearingError.lemma_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:49:02.687817+00:00
-- url     : https://prove2.me/theorems/de69cc05-c302-499e-9063-98894747b36a
-- title:
--   Lemma A.1, p. 20, (10) — the price-move term g(t) in terms of inverse moments of the Poisson count
-- statement:
--   In the one-auction model, let $N^{mm}$ be the Poisson($\mu$) market-maker counting process with arrival epochs $\tau^{mm}_k$, and $P_t=P_0+\sigma_f W_t$ the efficient price, with $W$ a Brownian motion independent of $N^{mm}$. For every $t>0$ the function
--   $$g(t)=\mathbb E\Big[\mathbf 1_{N^{mm}_t>0}\Big(\sum_{k=1}^{N^{mm}_t}\frac{P_{\tau^{mm}_k}-P_t}{N^{mm}_t}\Big)^2\Big]$$
--   is well defined (its integrand is integrable) and
--   $$g(t)=\sigma_f^2\,\frac{t^2}{2}\,\mu\,\mathbb E\Big[\frac1{(N^{mm}_t+1)^2}\Big]+\sigma_f^2\,\frac{t^3}{3}\,\mu^2\,\mathbb E\Big[\frac1{(N^{mm}_t+2)^2}\Big].$$
--
--   Together with Lemma A.2 (12) this gives $g$ in closed form, which produces the $\sigma_f^2$ terms of $E^{mid}(h)$ in Theorem 2.1.
--
--   **Formalization Note** The statement is posed under the full model hypotheses; only the Brownian motion, the Poisson arrivals and their independence enter. The $k$-th market maker of the page is `arrivalTime A k`; the sum runs over Lean indices $k=0,\dots,N-1$ with epoch `arrivalTime A (k+1)`.
-- source:
--   Jusselin, Mastrolia & Rosenbaum, Optimal auction duration: a price formation viewpoint, arXiv:1906.01713v3, p. 20, Lemma A.1, (10)

import Mathlib
import Definitions.Def_AuctionDuration_ClearingError_Model

namespace AuctionDuration.ClearingError
open MeasureTheory ProbabilityTheory QueueingFundamentals.Foundations

/-- Lemma A.1, p. 20, (10): for every t > 0,
g(t) = σ_f² (t²/2) µ E[1/(N^mm_t + 1)²] + σ_f² (t³/3) µ² E[1/(N^mm_t + 2)²]. -/
theorem lemma_A_1 {Ω : Type*} [MeasurableSpace Ω] (p : Params) (hp : p.Standing)
    (P : Measure Ω) (X : Auction Ω) (hX : IsModel p P X) (t : ℝ) (ht : 0 < t) :
    Integrable (fun ω => if 0 < Nmm X t ω then
        ((∑ k ∈ Finset.range (Nmm X t ω),
            (Peff p X (arrivalTime X.A (k + 1) ω) ω - Peff p X t ω)) / (Nmm X t ω : ℝ)) ^ 2
      else 0) P ∧
    gFun p P X t =
      p.sigmaF ^ 2 * (t ^ 2 / 2) * p.mu * ∫ ω, 1 / ((Nmm X t ω : ℝ) + 1) ^ 2 ∂P +
        p.sigmaF ^ 2 * (t ^ 3 / 3) * p.mu ^ 2 * ∫ ω, 1 / ((Nmm X t ω : ℝ) + 2) ^ 2 ∂P := by sorry

end AuctionDuration.ClearingError
