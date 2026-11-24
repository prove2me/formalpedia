-- Prove2me | Theorems.Thm_Formalism_HermitianLatticeCounting_P_s5b7_gram_cons
-- name    : Formalism.HermitianLatticeCounting.P.s5b7_gram_cons
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:43:15.177128+00:00
-- url     : https://prove2.me/theorems/850e18aa-2398-424a-9c0f-d2cfb6e7ce36
-- title:
--   P: s5b7 gram cons
-- statement:
--   The P construction uses the s5b7 gram cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L534-L574
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FlagUnipotentLattices/MinkowskiFactorialBounds/MeasurePreservingPiCompProd.lean#L534-L574

import Definitions.Def_Formalism_FlagUnipotentLattices_CardSubmodulesAndLinearEquivBounds
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_MeasurePreservingPiCompProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Module Matrix MeasureTheory Set
open scoped BigOperators ComplexConjugate

theorem Formalism.HermitianLatticeCounting.P.s5b7_gram_cons {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (r : ℕ) (v0 : V)
    (c : Fin r → ℂ) (w : Fin r → V) (hw : ∀ b, inner ℂ v0 (w b) = 0) :
    (Matrix.gram ℂ (Fin.cons v0 (fun b => c b • v0 + w b) : Fin (r + 1) → V)).det =
      ((‖v0‖ : ℂ) ^ 2) * (Matrix.gram ℂ w).det := by sorry
