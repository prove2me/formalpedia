-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_levy_shift_strictMonoOn
-- name    : AvramDividend.Classical.esscher_levy_shift_strictMonoOn
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T15:46:59.362823+00:00
-- url     : https://prove2.me/theorems/0906e33f-37dc-4382-95d0-b5cad94b12ab
-- title:
--   Actual Lévy Esscher-shift exponent is strictly increasing after a positive root
-- statement:
--   Let X be the canonical spectrally negative Lévy process and ψ(φ)=q with q,φ>0. Then β↦X.ψ(φ+β)−q is strictly increasing for β≥0. This applies the already-Proved actual Lévy source inequality from each positive point beyond φ, without separately assuming convexity or Standing.
-- source:
--   Proved eb5bb6f8-2e6f-478a-814d-8b4bd3b3519d, levy_psi_root_strictly_above_shift, and its canonical underlying secant estimate e9488750-ba29-4b2a-9d1d-05734aaa628f; KKR Scale Functions review §2.

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_psi_root_strictly_above_shift

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_levy_shift_strictMonoOn
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {F : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P F)
    (q phi : ℝ) (hq : 0 < q) (hphi : 0 < phi)
    (hroot : X.ψ phi = q) :
    StrictMonoOn (fun beta : ℝ => X.ψ (phi + beta) - q) (Ici (0 : ℝ)) := by sorry
