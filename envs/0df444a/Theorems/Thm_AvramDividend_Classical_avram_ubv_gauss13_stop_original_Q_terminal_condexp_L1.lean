-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_stop_original_Q_terminal_condexp_L1
-- name    : AvramDividend.Classical.avram_ubv_gauss13_stop_original_Q_terminal_condexp_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T22:36:36.330405+00:00
-- url     : https://prove2.me/theorems/e9233039-672e-427b-8dcf-e77cf3f30bdc
-- title:
--   Original Gaussian compensated square converges in L1 from a common terminal conditional-expectation representation
-- statement:
--   Direct physical-source L1 bridge for a338c453-58c0-411c-aaca-5cec689ed807 and 249c532d-4ec0-498c-81f0-b380dd476344. Q is explicitly the compensated square of the original pure Gaussian X.X, with no replacement Brownian process. If its physical ceiling samples Q(T_n) are conditional expectations of the same integrable terminal Q(B) on any sub-sigma-algebras of the original measurable space, and the physical clock/path squeeze gives almost-sure convergence to Q(sigma), then the source Q(T_n) converges to Q(sigma) in L1. The nontrivial step is uniform integrability of all conditional expectations of one fixed Q(B), followed by the pinned Mathlib Vitali L1 theorem. Proved 6258d525 supplies the exact conditional-expectation premise on genuine sampled ceiling K_n (provided each grid has the same final physical time B); Proved 23b87d40 plus clock squeeze supplies hAE. No floor of an arbitrary stopping clock is assumed. This is a necessary source component; the source-to-actual-controlled-multiplier passage, Stieltjes cash and stopping atoms remain separate.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_stop_original_Q_terminal_condexp_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (Q : ℝ≥0 → Ω → ℝ)
    (hQsource : ∀ t ω, Q t ω =
      (X.X t ω - (t : ℝ) * X.c) ^ 2 - (t : ℝ) * X.σ ^ 2)
    (B : ℝ≥0) (hQB : Integrable (Q B) P)
    (σ : Ω → ℝ≥0) (T : ℕ → Ω → ℝ≥0)
    (ℋ : ℕ → MeasurableSpace Ω)
    (hℋ : ∀ n, ℋ n ≤ mΩ)
    (hCE : ∀ n, (fun ω => Q (T n ω) ω) =ᵐ[P]
      condExp (ℋ n) P (Q B))
    (hAE : ∀ᵐ ω ∂P,
      Tendsto (fun n => Q (T n ω) ω) atTop
        (nhds (Q (σ ω) ω))) :
    Tendsto (fun n =>
      eLpNorm (fun ω => Q (T n ω) ω - Q (σ ω) ω) 1 P)
      atTop (nhds 0) := by
  sorry
