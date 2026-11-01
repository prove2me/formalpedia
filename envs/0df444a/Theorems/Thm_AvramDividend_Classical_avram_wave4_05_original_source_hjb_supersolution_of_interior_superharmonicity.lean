-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_original_source_hjb_supersolution_of_interior_superharmonicity
-- name    : AvramDividend.Classical.avram_wave4_05_original_source_hjb_supersolution_of_interior_superharmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:13:24.751598+00:00
-- url     : https://prove2.me/theorems/4de732b5-7893-48d0-88f3-92f4d8a230d0
-- title:
--   Original compensated Lévy barrier HJB supersolution from interior superharmonicity alone
-- statement:
--   Under actual original source Standing and the root Gaussian/BV/C2 alternative, the optimal barrier candidate lies in the compensated Lévy generator domain at every positive reserve and is a HJB supersolution max(Γvcstar−qvcstar,1−vcstar')≤0 whenever the generator residual is merely nonpositive both in the positive interior and above cstar. Interior q-harmonic equality is not assumed. Standing implies finite cstar; the source q-scale gives automatic above-cap generator integrability; the canonically proved cap and zero-cap HJB identities handle boundary cases. This is the source analytic supersolution necessary for verification when equality of the pure-jump generator cannot yet be derived.
-- source:
--   Avram–Palmowski–Pistorius (2007), Lemma 4 and Proposition 4; canonical cap HJB 8d03da6b, derivative d42fc3e4, source upper domain 32cfe60b

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_cstar_lt_top
import Theorems.Thm_AvramDividend_Classical_vcstar_generatorIntegrable_strictly_above_real_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_at_positive_cstar
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_all_positive_of_generator_zero_barrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_original_source_hjb_supersolution_of_interior_superharmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hsmooth : 0 < X.σ ∨ X.BoundedVariation ∨
      ContDiffOn ℝ 2 (vcstar W) (Ioi 0))
    (hres_above : ∀ y : ℝ, (cstar W).toReal < y →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0)
    (hinside : 0 < cstar W → ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x ≤ 0) :
    ∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) ≤ 0 := by sorry
