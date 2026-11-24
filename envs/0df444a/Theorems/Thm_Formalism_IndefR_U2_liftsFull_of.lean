-- Prove2me | Theorems.Thm_Formalism_IndefR_U2_liftsFull_of
-- name    : Formalism.IndefR.U2.liftsFull_of
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:19:21.230414+00:00
-- url     : https://prove2.me/theorems/19c212a5-9b1c-40cc-8d3b-863b2b4e0dae
-- title:
--   U2: lifts Full of
-- statement:
--   The U2 construction uses the lifts Full of property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L76-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteReal/NormalDecomposition/DecompOfNormalStatement.lean#L76-L111

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteReal_NormalDecomposition_DecompOfNormalStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped InnerProductSpace
noncomputable section
open Formalism Formalism.IndefR Formalism.IndefR.U2
variable {I : Type*} {A B : Type*}
  [NormedAddCommGroup A] [InnerProductSpace ℂ A] [NormedAddCommGroup B] [InnerProductSpace ℂ B]
variable {θ : A →ₗ[ℂ] B} {θa : B →ₗ[ℂ] A} {op : I → Module.End ℂ A} {opB : I → Module.End ℂ B}
  {good : Submodule ℂ A} {goodB : Submodule ℂ B} {Ix : Set (I → ℂ)}

theorem Formalism.IndefR.U2.liftsFull_of (hD : OrthDecomp op good Ix) (hI : Intw θ op opB) (hG : GoodIn θ good goodB)
    (hA : IsAdj θ θa) (hO : OntoParts θa op opB good goodB Ix) : LiftsFull θ op opB good goodB Ix := by sorry
