-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_shifted_positive_derivative_exists
-- name    : AvramDividend.Classical.avram_ws01e_cr_new_shifted_positive_derivative_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T21:48:42.264235+00:00
-- url     : https://prove2.me/theorems/0385f777-7103-4c2b-a6e1-b7483de69ec6
-- title:
--   Strict positive derivative at every positive shift of an actual Lévy positive q-root
-- statement:
--   For the canonical spectrally negative Lévy process, if ψ(phi)=q>0 with phi>0 and lam>0, the exponent has a genuine two-sided HasDerivAt derivative m>0 at phi+lam. Derivative existence follows from already-Proved source-specific analyticOnNhd of the shifted exponent derived through the true time-one exponential-moment cumulant generator. The positive value follows from already-Proved source-specific strict shift and positive-root derivative bound. No Standing, independent clock, right-secant-only shortcut, or extra moment hypothesis.
-- source:
--   Accepted 4dddb6f2-c657-46f9-89ae-291bb1ef0a23 (source-specific real analyticity via the exact SpectrallyNegativeLevy.laplace field and pinned Mathlib ProbabilityTheory.analyticOnNhd_cgf), 7e3b59e7-6d4f-4dbc-a2be-f9c95cabecbb (positive actual q-root derivative once HasDerivAt), and eb5bb6f8-2e6f-478a-814d-8b4bd3b3519d (strict exponent increase after positive root).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_shifted_levy_psi_analytic_on_positive
import Theorems.Thm_AvramDividend_Classical_esscher_levy_positive_root_derivative_lower
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_cr_new_shifted_positive_derivative_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q phi lam : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) (hlam : 0 < lam) :
    ∃ m : ℝ, 0 < m ∧ HasDerivAt X.ψ m (phi + lam) := by sorry
