-- Prove2me | Theorems.Thm_DensInertW_iso_fiber
-- name    : DensInertW.iso_fiber
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:53:25.563554+00:00
-- url     : https://prove2.me/theorems/23e58eaf-8ac2-46d9-abe9-884e042ad927
-- title:
--   Dens Inert W: iso fiber
-- statement:
--   The Dens Inert W construction uses the iso fiber property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/IsoPeel.lean#L67-L146
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/IsoPeel.lean#L67-L146

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ExistsTraceNeZero
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_IsoPeel
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

theorem DensInertW.iso_fiber [Fintype L] {n c q : ℕ} {M : Matrix (Fin n) (Fin n) L}
    (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q) (hinv : ∀ a : L, (a ^ q) ^ q = a)
    (hM : IsHerm q M) (W : Submodule L (Fin n → L)) (x y : Fin n → L)
    (hxW : x ∈ W) (hyW : y ∈ W) (hxx : hf q M x x = 0) (hxy : hf q M x y = 1) :
    (Finset.univ.filter (fun X : Fin (c + 1) → Fin n → L => isoP q M W X ∧ X 0 = x)).card =
      Fintype.card (Fin c → L) * (Finset.univ.filter (isoP (m := c) q M
        (W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y)))).card := by sorry
