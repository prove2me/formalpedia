-- Prove2me | Theorems.Thm_DensInertW_an_fiber
-- name    : DensInertW.an_fiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:38:39.298797+00:00
-- url     : https://prove2.me/theorems/4dbf5890-fe72-4d2a-b48d-470fdb66e298
-- title:
--   Dens Inert W: an fiber
-- statement:
--   The Dens Inert W construction uses the an fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/AnisoPeel.lean#L31-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/AnisoPeel.lean#L31-L96

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
noncomputable section
open DensInertW
open DensInertW.Sub
variable {L : Type} [Field L]
open Classical

theorem DensInertW.an_fiber [Fintype L] {n m q : ℕ} {M : Matrix (Fin n) (Fin n) L}
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : IsHerm q M) (W : Submodule L (Fin n → L)) (b : L) (w : Fin m → L) (x : Fin n → L)
    (hxW : x ∈ W) (hxx : hf q M x x = b) (hb : b ≠ 0) :
    (Finset.univ.filter (fun X : Fin (m + 1) → Fin n → L =>
        anP q M W (Matrix.diagonal (Fin.cons b w : Fin (m + 1) → L)) X ∧ X 0 = x)).card =
      (Finset.univ.filter (anP q M (W ⊓ LinearMap.ker (hfL q M x)) (Matrix.diagonal w))).card := by sorry
