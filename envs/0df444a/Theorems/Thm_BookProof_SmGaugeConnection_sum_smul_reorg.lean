-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_sum_smul_reorg
-- name    : BookProof.SmGaugeConnection.sum_smul_reorg
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:55:08.807979+00:00
-- url     : https://prove2.me/theorems/71d46f33-b88f-4344-a13c-34c97f9104a5
-- title:
--   `BookProof.SmGaugeConnection.sum_smul_reorg` (x : Fin d → Fin d → ℂ) (y : Fin d → Fin d → Fin d → ℂ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ) : ∑ a : Fin d, ∑ b : Fin d, x a...
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.sum_smul_reorg` (x : Fin d → Fin d → ℂ) (y : Fin d → Fin d → Fin d → ℂ) (T : Fin d → Matrix (Fin N) (Fin N) ℂ) : ∑ a : Fin d, ∑ b : Fin d, x a b • (Complex.I • ∑ c : Fin d, y a b c • T c) = ∑ c : Fin d, (∑ a : Fin d, ∑ b : Fin d, Complex.I * (x a b * y a b c)) • T c
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.sum_smul_reorg`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.sum_smul_reorg
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterFarisLavine
import Mathlib
import Definitions.Def_ChapterSmGaugeConnection
open BookProof.SmGaugeConnection



open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}

theorem BookProof.SmGaugeConnection.sum_smul_reorg (x : Fin d → Fin d → ℂ) (y : Fin d → Fin d → Fin d → ℂ)
    (T : Fin d → Matrix (Fin N) (Fin N) ℂ) :
    ∑ a : Fin d, ∑ b : Fin d, x a b • (Complex.I • ∑ c : Fin d, y a b c • T c)
      = ∑ c : Fin d, (∑ a : Fin d, ∑ b : Fin d, Complex.I * (x a b * y a b c)) • T c := by sorry
