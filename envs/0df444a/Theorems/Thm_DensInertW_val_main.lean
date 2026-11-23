-- Prove2me | Theorems.Thm_DensInertW_val_main
-- name    : DensInertW.val_main
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T10:09:17.755041+00:00
-- url     : https://prove2.me/theorems/4f57294d-6897-48af-8e9e-536ca52704d4
-- title:
--   Dens Inert W: val main
-- statement:
--   The Dens Inert W construction uses the val main property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ValMain.lean#L163-L226
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/ValMain.lean#L163-L226

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankValPerp
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_ValMain
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
variable {K L : Type} [Field K] [Fintype K] [Field L] [Fintype L] [Algebra K L] {n : ℕ}
  {M : Matrix (Fin n) (Fin n) L}
open Classical

theorem DensInertW.val_main (h2 : finrank K L = 2) (hM : IsHerm (Fintype.card K) M) :
    ∀ (d : ℕ) (W : Submodule L (Fin n → L)), NonDeg (Fintype.card K) M W →
      finrank L W = d → ∀ a : L, a ^ Fintype.card K = a →
        ((({v | v ∈ W ∧ hf (Fintype.card K) M v v = a} : Set (Fin n → L)).ncard : ℕ) : ℤ) =
          if a = 0 then valZ (Fintype.card K) d else valN (Fintype.card K) d := by sorry
