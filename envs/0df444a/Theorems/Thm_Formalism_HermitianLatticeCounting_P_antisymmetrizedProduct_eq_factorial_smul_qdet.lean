-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_antisymmetrizedProduct_eq_factorial_smul_qdet
-- name    : Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_eq_factorial_smul_qdet
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:35:06.117801+00:00
-- url     : https://prove2.me/theorems/0d75af00-e3b3-4b97-b512-004a926d9081
-- title:
--   P: antisymmetrized Product eq factorial smul qdet
-- statement:
--   The P construction uses the antisymmetrized Product eq factorial smul qdet property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/AntisymmetrizedProductEqFactorialSmulQdet.lean#L187-L229
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/AntisymmetrizedProductEqFactorialSmulQdet.lean#L187-L229

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

theorem Formalism.HermitianLatticeCounting.P.antisymmetrizedProduct_eq_factorial_smul_qdet {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (u : ℂ) :
    doublyAntisymmetrizedProduct E (fun k => u - (k : ℂ)) = (n.factorial : ℂ) • qdet E u := by sorry
