-- Prove2me | Theorems.Thm_Formalism_MainNotions_S_Loc_Pt_cast_blocks
-- name    : Formalism.MainNotions.S.Loc.Pt.cast_blocks
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:18:13.733324+00:00
-- url     : https://prove2.me/theorems/3e6d47df-b000-4f44-8da1-a96d493647c5
-- title:
--   Pt: cast blocks
-- statement:
--   The Pt construction uses the cast blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/FractionFieldToGenericStalkAlgebraMapEq.lean#L263-L263
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/CuspSpanNormBounds/FractionFieldToGenericStalkAlgebraMapEq.lean#L263-L263

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_Point
import Definitions.Def_Formalism_SharpRestriction_CuspSpanNormBounds_FractionFieldToGenericStalkAlgebraMapEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open ComplexConjugate
open Formalism Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Loc
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
open Formalism.MainNotions.S.Loc.Pt

theorem Formalism.MainNotions.S.Loc.Pt.cast_blocks {n n' : ℕ} (e : n = n') (w : Pt E n) : (w.cast e).blocks = w.blocks := by sorry

attribute [defeq] Formalism.MainNotions.S.Loc.Pt.cast_blocks
