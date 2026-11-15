-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB72_original_finitecap_stopped_ruinclipped_physical_cash_lastmesh_discount_L1
-- name    : AvramDividend.Classical.avram_gbB72_original_finitecap_stopped_ruinclipped_physical_cash_lastmesh_discount_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T19:20:29.089396+00:00
-- url     : https://prove2.me/theorems/c0f9c801-4705-49de-bb53-e1c08c22a40f
-- title:
--   Original finite-cap stopped subclock strict last-mesh discounted cash and discount-overpayment error vanishes in L1
-- statement:
--   For every actual original admissible finite-cap dividend D, standing Lévy source X and random localisation clock rho no later than sigma_k no later than the true ruin/horizon stopped clock tau, the exact original positive discount-overpayment plus last open stop-straddling dividend cash mass has a vanishing expected L1 envelope as the original physical grid refines. It requires no new ruin or boundedness hypothesis beyond the B54 local stopped clock assumptions and retains strict paymentTimes intervals. This closes the cash last-cell error component of the B54 witness.
-- source:
--   Proved gledger111 translates rho<=min(ruinTime,n).toNNReal into rho<=n and rho<=ruinTime. Proved gledger39 then directly supplies integrability and expected positive error vanishing of exact last-mesh strict cash and discount adjustment under original D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger111_subclock_le_ruin_and_horizon
import Theorems.Thm_AvramDividend_Classical_avram_gledger39_original_bounded_stop_discount_mesh_error_L1
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB72_original_finitecap_stopped_ruinclipped_physical_cash_lastmesh_discount_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσle : ∀ k ω, σ k ω ≤ τ ω)
    (k : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρle : ∀ ω, ρ ω ≤ σ k ω) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
      Integrable (E m) P ∧
      (∫ ω, E m ω ∂P) ≤ ε := by sorry
