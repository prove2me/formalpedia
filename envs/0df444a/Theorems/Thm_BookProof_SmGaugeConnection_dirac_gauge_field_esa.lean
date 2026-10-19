-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_dirac_gauge_field_esa
-- name    : BookProof.SmGaugeConnection.dirac_gauge_field_esa
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:55:28.52798+00:00
-- url     : https://prove2.me/theorems/b94cd53e-a5e1-4413-b47e-6fb992cafb24
-- title:
--   `BookProof.SmGaugeConnection.dirac_gauge_field_esa` {k : Fin 3 → ℝ} {m1 m2 g : ℝ} {T : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {A : Fin 8 → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) {om : Fin
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.dirac_gauge_field_esa` {k : Fin 3 → ℝ} {m1 m2 g : ℝ} {T : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {A : Fin 8 → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a) {om : Fin 12 → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) : EssentiallySelfAdjointOn (fullDom 12) ((onFull (smFermiHam (Matrix.reindex modeEquiv modeEquiv (diracGaugeMat k m1 m2 g T A)) (0 : Matrix (Fin 12) (Fin 12) ℂ) 0)).comp (Submodule.inclusion (le_refl (fullDom 12))))
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.dirac_gauge_field_esa`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.dirac_gauge_field_esa
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmGaugeConnection
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
open BookProof.SmCar
open BookProof.SmDiracYukawa
open BookProof.SmGaugeConnection



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}

theorem BookProof.SmGaugeConnection.dirac_gauge_field_esa {k : Fin 3 → ℝ} {m1 m2 g : ℝ}
    {T : Fin 8 → Matrix (Fin 3) (Fin 3) ℂ} {A : Fin 8 → Fin 3 → ℝ} (hT : ∀ a, (T a)ᴴ = T a)
    {om : Fin 12 → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) :
    EssentiallySelfAdjointOn (fullDom 12)
      ((onFull (smFermiHam (Matrix.reindex modeEquiv modeEquiv (diracGaugeMat k m1 m2 g T A))
          (0 : Matrix (Fin 12) (Fin 12) ℂ) 0)).comp
        (Submodule.inclusion (le_refl (fullDom 12)))) := by sorry
