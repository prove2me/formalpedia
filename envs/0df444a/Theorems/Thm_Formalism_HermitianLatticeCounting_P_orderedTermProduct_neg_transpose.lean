-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_orderedTermProduct_neg_transpose
-- name    : Formalism.HermitianLatticeCounting.P.orderedTermProduct_neg_transpose
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:42:14.934271+00:00
-- url     : https://prove2.me/theorems/8ece170f-2b3e-4a0e-a181-551b71234721
-- title:
--   P: ordered Term Product neg transpose
-- statement:
--   The P construction uses the ordered Term Product neg transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/AntisymmetrizedProductEqFactorialSmulQdet.lean#L241-L249
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/AntisymmetrizedProductEqFactorialSmulQdet.lean#L241-L249

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

theorem Formalism.HermitianLatticeCounting.P.orderedTermProduct_neg_transpose {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (arg : Fin n → ℂ)
    (σ τ : Equiv.Perm (Fin n)) :
    orderedTermProduct (fun a b => -E b a) arg σ τ = (-1) ^ n * orderedTermProduct E (fun k => -arg k) τ σ := by sorry
