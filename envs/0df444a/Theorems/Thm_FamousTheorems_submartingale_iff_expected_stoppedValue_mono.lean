-- Prove2me | Theorems.Thm_FamousTheorems_submartingale_iff_expected_stoppedValue_mono
-- name    : FamousTheorems.submartingale_iff_expected_stoppedValue_mono
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-21T23:45:31.109332+00:00
-- url     : https://prove2.me/theorems/79c82d02-41f6-4fcc-9401-e0782278ae9e
-- title:
--   The fair games theorem (optional stopping)
-- statement:
--   **The fair games theorem**, in the form of Doob's optional stopping theorem.
--
--   Let $f$ be an adapted, integrable process on a filtered probability space. Then $f$ is a
--   submartingale if and only if for every pair of bounded stopping times $\tau \le \sigma$,
--   $$\mathbb{E}\bigl[f_\tau\bigr] \;\le\; \mathbb{E}\bigl[f_\sigma\bigr].$$
--
--   Read left to right this says you cannot beat an unfavourable game by clever timing: no stopping rule
--   based only on information available so far can improve the expected payoff. Read right to left it
--   says this "no strategy helps" property actually characterises submartingales — the two formulations
--   carry the same information. For a martingale both inequalities hold, so the expectation is constant
--   across all bounded stopping times, which is the precise sense in which a fair game stays fair.
--
--   The boundedness hypothesis is essential rather than technical. Without it the gambler's doubling
--   strategy — keep doubling the stake until the first win — is a stopping time that turns a fair game
--   into a sure profit, which is why casinos impose table limits and why the unbounded case needs
--   uniform integrability.
--
--   Doob developed the theory in the 1940s and 50s; optional stopping is the tool behind the classical
--   ruin problems, Wald's identity, and much of mathematical finance, where it is the reason no-arbitrage
--   pricing works.
--
--   **Formalization note.** `Filtration ℕ m0` is the increasing family of $\sigma$-algebras, stopping
--   times take values in `ℕ∞`, and `stoppedValue f τ` is $\omega \mapsto f_{\tau(\omega)}(\omega)$. The
--   result is Mathlib's `MeasureTheory.submartingale_iff_expected_stoppedValue_mono`.
-- source:
--   One of Freek Wiedijk's "100 theorems"; formalized in Mathlib. Proof here reduces to the corresponding Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory Filter Set intervalIntegral
open scoped Real Topology ENNReal

theorem submartingale_iff_expected_stoppedValue_mono {Ω : Type*} {m0 : MeasurableSpace Ω}
    {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ} [SigmaFiniteFiltration μ 𝒢]
    (hadp : StronglyAdapted 𝒢 f) (hint : ∀ i, Integrable (f i) μ) :
    Submartingale f 𝒢 μ ↔ ∀ τ σ : Ω → ℕ∞, IsStoppingTime 𝒢 τ → IsStoppingTime 𝒢 σ →
      τ ≤ σ → (∃ N : ℕ, ∀ x, σ x ≤ N) → μ[stoppedValue f τ] ≤ μ[stoppedValue f σ] := by sorry

end FamousTheorems
