-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb72_original_topcap_predictable_negative_mark_uniform_bound
-- name    : AvramDividend.Classical.avram_bvb72_original_topcap_predictable_negative_mark_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T17:51:35.40453+00:00
-- url     : https://prove2.me/theorems/0abe9774-8bce-47a4-809b-3fd1538b853a
-- title:
--   Exact original topcap finite negative-activity predictable marked integral V(n) is uniformly bounded by its finite physical Lévy intensity and horizon
-- statement:
--   For the literal original topcap finite negative activity filtered bounded-variation source and the original strict T−δ_n marked jump kernel H_n, the absolute predictable intensity-integral V_n over the physical interval 0≤t≤T is bounded almost surely for every mesh row by one deterministic constant K times ν((−∞,0)).toReal×T. The deterministic K comes from the already-Proved original topcap pathwise uniform mark kernel bound; finite source negative jump intensity and the finite physical horizon give the product-measure estimate. This is the missing predictable compensator envelope for the integrable domination part of BVB70.
-- source:
--   Proved BVB original uniform marked kernel bound 9abb3b39, Proved topcap original V_n integrable 73b687ec, Mathlib norm_integral_le_of_norm_le_const and finite measure restrictions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb72_original_topcap_predictable_negative_mark_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hCapTop : C = ⊤)
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
    let J : ℕ → Ω → ℝ := fun n ω =>
      ∫ p, H n ((p.1, ω), p.2) ∂(NX ω)
    let V : ℕ → Ω → ℝ := fun n ω =>
      ∫ t, ∫ z, H n ((t, ω), z) ∂(X.ν.restrict (Iio (0 : ℝ)))
        ∂(((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ n : ℕ, ∀ᵐ ω ∂P,
        ‖V n ω‖ ≤ K * ((X.ν (Iio (0 : ℝ))).toReal * T) := by sorry
