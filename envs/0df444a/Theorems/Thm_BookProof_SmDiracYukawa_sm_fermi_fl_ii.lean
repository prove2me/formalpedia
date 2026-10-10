-- Prove2me | Theorems.Thm_BookProof_SmDiracYukawa_sm_fermi_fl_ii
-- name    : BookProof.SmDiracYukawa.sm_fermi_fl_ii
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-09T17:49:28.576091+00:00
-- url     : https://prove2.me/theorems/eff25830-9b06-44e4-87b3-82b66e3b66c1
-- title:
--   `BookProof.SmDiracYukawa.sm_fermi_fl_ii` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) : |commForm (onFull (smFermiHam hD M z)) (onFull (smFermiN om c0)) x| ≤ (2 * smFermiBo
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmDiracYukawa`.
--
--   `BookProof.SmDiracYukawa.sm_fermi_fl_ii` (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) : |commForm (onFull (smFermiHam hD M z)) (onFull (smFermiN om c0)) x| ≤ (2 * smFermiBound hD M z * smFermiOm om c0) * quadForm (onFull (smFermiN om c0)) x
--
--   Formalization note: Lean 4 identifier `BookProof.SmDiracYukawa.sm_fermi_fl_ii`.

-- Generated from ChapterSmDiracYukawa.lean — theorem BookProof.SmDiracYukawa.sm_fermi_fl_ii
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterFarisLavineCore
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmCar
open BookProof.SmDiracYukawa



open Finset Matrix
open BookProof.SmCar BookProof.FarisLavine

variable {n : ℕ}

noncomputable section

variable {hD M : Matrix (Fin n) (Fin n) ℂ} {z : ℂ} {om : Fin n → ℝ} {c0 : ℝ}

theorem BookProof.SmDiracYukawa.sm_fermi_fl_ii (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) (x : fullDom n) :
    |commForm (onFull (smFermiHam hD M z)) (onFull (smFermiN om c0)) x|
      ≤ (2 * smFermiBound hD M z * smFermiOm om c0)
        * quadForm (onFull (smFermiN om c0)) x := by sorry
