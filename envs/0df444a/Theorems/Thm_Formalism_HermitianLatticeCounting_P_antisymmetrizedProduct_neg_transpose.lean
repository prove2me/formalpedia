-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_antisymmetrizedProduct_neg_transpose
-- name    : Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_neg_transpose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:30.544099+00:00
-- url     : https://prove2.me/theorems/aafe98a5-dc84-4aab-a9fc-1c8747f6a440
-- title:
--   P: antisymmetrized Product neg transpose
-- statement:
--   The P construction uses the antisymmetrized Product neg transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/AntisymmetrizedProductEqFactorialSmulQdet.lean#L251-L262
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/AntisymmetrizedProductEqFactorialSmulQdet.lean#L251-L262

import Definitions.Def_Formalism_FlagUnipotentLattices_QDetNegTranspose
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_LanglandsParameterEquivariant
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ShiftedGeneratorEqIteSmulAdd
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_AntisymmetrizedProductEqFactorialSmulQdet
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.HermitianLatticeCounting.S8 Formalism.REAL TensorProduct Finset
set_option linter.all false
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P

theorem Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ) :
    doublyAntisymmetrizedProduct (fun a b => -E b a) arg = (-1) ^ n * doublyAntisymmetrizedProduct E (fun k => -arg k) := by sorry
