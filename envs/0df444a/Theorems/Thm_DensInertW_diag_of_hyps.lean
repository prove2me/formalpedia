-- Prove2me | Theorems.Thm_DensInertW_diag_of_hyps
-- name    : DensInertW.diag_of_hyps
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:57.209528+00:00
-- url     : https://prove2.me/theorems/32305fd3-c7b8-48a1-9896-ef2a59a1e0cd
-- title:
--   Dens Inert W: diag of hyps
-- statement:
--   The Dens Inert W construction uses the diag of hyps property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/HermitianDiagonalization.lean#L87-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/HermitianDiagonalization.lean#L87-L107

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_HermitianDiagonalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW
open DensInertW.Sub
variable {L : Type} [Field L]

theorem DensInertW.diag_of_hyps {m q : ℕ} (B : Matrix (Fin m) (Fin m) L)
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hB : IsHerm q B) (htr : ∀ z : L, z ≠ 0 → ∃ c : L, c * z + (c * z) ^ q ≠ 0) :
    ∃ P : Matrix (Fin m) (Fin m) L, IsUnit P.det ∧ ∃ (w : Fin m → L) (r : ℕ), r ≤ m ∧
        P * B * (P.map (fun y => y ^ q)).transpose = Matrix.diagonal w ∧
        (∀ i, w i ≠ 0 ↔ i.val < r) ∧ (∀ i, w i ^ q = w i) := by sorry
