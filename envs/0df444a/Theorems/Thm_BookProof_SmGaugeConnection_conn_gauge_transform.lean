-- Prove2me | Theorems.Thm_BookProof_SmGaugeConnection_conn_gauge_transform
-- name    : BookProof.SmGaugeConnection.conn_gauge_transform
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-10T13:54:53.763253+00:00
-- url     : https://prove2.me/theorems/8ef9f099-30ec-4e07-8564-38fece454089
-- title:
--   `BookProof.SmGaugeConnection.conn_gauge_transform` {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ} {A : Fin d → Fin 3 → ℝ} {U : Matrix (Fin N) (Fin N) ℂ} {R : Fin d → Fin d → ℝ} (hU
-- statement:
--   Prove the following Lean 4 theorem from `ChapterSmGaugeConnection`.
--
--   `BookProof.SmGaugeConnection.conn_gauge_transform` {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ} {A : Fin d → Fin 3 → ℝ} {U : Matrix (Fin N) (Fin N) ℂ} {R : Fin d → Fin d → ℝ} (hUT : ∀ a, U * T a * Uᴴ = ∑ b : Fin d, ((R a b : ℝ) : ℂ) • T b) (j : Fin 3) : U * conn g T A j * Uᴴ = conn g T (fun b i => ∑ a : Fin d, R a b * A a i) j
--
--   Formalization note: Lean 4 identifier `BookProof.SmGaugeConnection.conn_gauge_transform`.

-- Generated from ChapterSmGaugeConnection.lean — theorem BookProof.SmGaugeConnection.conn_gauge_transform
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

theorem BookProof.SmGaugeConnection.conn_gauge_transform {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ}
    {A : Fin d → Fin 3 → ℝ} {U : Matrix (Fin N) (Fin N) ℂ} {R : Fin d → Fin d → ℝ}
    (hUT : ∀ a, U * T a * Uᴴ = ∑ b : Fin d, ((R a b : ℝ) : ℂ) • T b) (j : Fin 3) :
    U * conn g T A j * Uᴴ = conn g T (fun b i => ∑ a : Fin d, R a b * A a i) j := by sorry
