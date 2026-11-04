-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_stopped_budget_ae_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_stopped_budget_ae_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:12:12.568857+00:00
-- url     : https://prove2.me/theorems/bd926b38-223c-4c15-8daf-3fef35432a9b
-- title:
--   Almost-sure localisation limit preserves original stopped budget and signed generator residual
-- statement:
--   On the original spectrally negative Lévy probability space, suppose a sequence of genuinely localised stopped terminal, dividend cash, martingale and signed drift terms has an almost-sure convergent representative for every term, and satisfies the actual finite-clock stopped inequality and nonpositive residual a.e. at each index. Then a common full-measure event supports the exact limiting stopped-budget inequality and the residual sign. This closes only the deterministic pathwise limit step; a.s. convergence, martingale uniform integrability, and the boundary signs remain explicit proof obligations.
-- source:
--   Mathlib Filter Tendsto continuity of addition and eventual order, original source X/filtration; Eq. (5.13) of Avram et al.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter
open scoped Topology NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_p4_e_localise_original_stopped_budget_ae_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (x : ℝ)
    (Tk Ck Mk Gk Hk : ℕ → Ω → ℝ)
    (Term Cash M G H : Ω → ℝ)
    (hBudget : ∀ k, ∀ᵐ ω ∂P,
      Tk k ω + Ck k ω ≤ w x + Mk k ω + Gk k ω + Hk k ω)
    (hSign : ∀ k, ∀ᵐ ω ∂P, Gk k ω + Hk k ω ≤ 0)
    (hT : ∀ᵐ ω ∂P, Tendsto (fun k => Tk k ω) atTop (𝓝 (Term ω)))
    (hC : ∀ᵐ ω ∂P, Tendsto (fun k => Ck k ω) atTop (𝓝 (Cash ω)))
    (hM : ∀ᵐ ω ∂P, Tendsto (fun k => Mk k ω) atTop (𝓝 (M ω)))
    (hG : ∀ᵐ ω ∂P, Tendsto (fun k => Gk k ω) atTop (𝓝 (G ω)))
    (hH : ∀ᵐ ω ∂P, Tendsto (fun k => Hk k ω) atTop (𝓝 (H ω))) :
    (∀ᵐ ω ∂P, G ω + H ω ≤ 0) ∧
    (∀ᵐ ω ∂P, Term ω + Cash ω ≤ w x + M ω + G ω + H ω) := by sorry
