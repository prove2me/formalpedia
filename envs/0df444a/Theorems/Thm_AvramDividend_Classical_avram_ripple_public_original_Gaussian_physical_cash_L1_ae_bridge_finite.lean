-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ripple_public_original_Gaussian_physical_cash_L1_ae_bridge_finite
-- name    : AvramDividend.Classical.avram_ripple_public_original_Gaussian_physical_cash_L1_ae_bridge_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T19:32:18.141629+00:00
-- url     : https://prove2.me/theorems/bd105376-770b-4f86-bf4a-7c7adf81f10f
-- title:
--   Finite-measure original physical Gaussian stopped cash L1 and error-to-a.e. bridge
-- statement:
--   Source-faithful measure-theoretic bridge for the original stopped finitecap discounted dividend cash: given genuine globally integrable original payoff F and Gaussian mesh M_m, original restricted occupation charge Occ, true globally integrable Gaussian L1 limit N, exact original-event physical-cell Ito/Stieltjes upper ledger with integrable nonnegative E_m and vanishing original-event expected E_m, conclude F−x≤N+Γ+c Occ a.e. on the original stopped event and restricted global Gaussian L1 mesh convergence. This isolates deterministic L1 transfer from the physical Ito/Stieltjes source in the original Avram mission and reuses already Proved publicly importable exact bridges. The ambient measure P is finite, as guaranteed in the original Avram Lévy model by X.isProbability.
-- source:
--   Original Proved signed one-sided public ae L1 transfer bdbc1492, discount cash integral certificate b8e914fe, Gaussian global-to-restricted L1 0c70b510; original Avram Gaussian finitecap c46fb312.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ripple_public_signed_L1_mesh_ae_upper
import Theorems.Thm_AvramDividend_Classical_avram_ga_discount_cash_integrable_finite_measure
import Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_global_GH_L1_limit_restricts_to_future_tube
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem AvramDividend.Classical.avram_ripple_public_original_Gaussian_physical_cash_L1_ae_bridge_finite
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P]
    (A : Set Ω) (hA : MeasurableSet A)
    (F N Occ : Ω → ℝ) (M E : ℕ → Ω → ℝ) (x Γ c : ℝ)
    (hFI : Integrable F P) (hMI : ∀ m, Integrable (M m) P)
    (hOI : Integrable Occ (P.restrict A)) (hNI : Integrable N P)
    (hEI : ∀ m, Integrable (E m) (P.restrict A))
    (hEpos : ∀ m, ∀ᵐ ω ∂(P.restrict A), 0 ≤ E m ω)
    (hEL1 : Tendsto (fun m => ∫ ω in A, E m ω ∂P) atTop (nhds (0 : ℝ)))
    (hML1 : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂P)
      atTop (nhds (0 : ℝ)))
    (hCash : ∀ m, ∀ᵐ ω ∂(P.restrict A),
      F ω - x - (Γ + c * Occ ω) ≤ M m ω + E m ω) :
    (∀ᵐ ω ∂(P.restrict A), F ω - x ≤ N ω + Γ + c * Occ ω) ∧
    Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (nhds (0 : ℝ)) := by sorry
