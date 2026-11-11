-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys61_original_finiteactivity_compensated_source_uniform_lower
-- name    : AvramDividend.Classical.avram_bvb_phys61_original_finiteactivity_compensated_source_uniform_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:29:47.436649+00:00
-- url     : https://prove2.me/theorems/3269e819-c6c8-4220-ade3-3ee5f22131fc
-- title:
--   Original finite-activity compensated physical marked source has one integrable lower envelope
-- statement:
--   The exact same-space original-X/D compensated negative-jump source M_n has a common P-integrable lower bound. Combine the proved original marked integral |J_n|≤K*N_T with N_T integrable (9a6793e4), and a uniform deterministic bound for the finite-activity Lévy compensator V_n using the finite-cap kernel bound cf0d73ae, ν(Iio0)<∞ and the physical time window [0,T]. This is the remaining genuine stochastic component required by 524afc4a and the root-connected physical-grid majorant c4f4edb5.
-- source:
--   Original BV physical finite-activity source route, needed for 524afc4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys61_original_finiteactivity_compensated_source_uniform_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 < T)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤) :
    let δ : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
    let U : ℝ≥0 → Ω → ℝ := fun t ω => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
    let H : ℕ → (ℝ≥0 × Ω) × ℝ → ℝ := fun n p =>
      if 0 < p.1.1 ∧ (p.1.1 : ℝ) < T - δ n ∧
         (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
         0 ≤ U p.1.1 p.1.2 ∧ ENNReal.ofReal (U p.1.1 p.1.2) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (U p.1.1 p.1.2 + p.2) - w (U p.1.1 p.1.2)) else 0
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {t : ℝ≥0 | 0 < t ∧ X.X t ω -
        Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ≠ 0}).map
        (fun t : ℝ≥0 => (t, X.X t ω -
          Function.leftLim (fun s : ℝ≥0 => X.X s ω) t)))
    let M : ℕ → Ω → ℝ := fun n ω =>
      (∫ p, H n ((p.1, ω), p.2) ∂(NX ω)) -
        (∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
          ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal))
    ∃ K : Ω → ℝ, Integrable K P ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P, -K ω ≤ M n ω := by sorry
