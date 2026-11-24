-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefLink2_forget
-- name    : Formalism.L2.Indef.IndefLink2.forget
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:46.5698+00:00
-- url     : https://prove2.me/theorems/611b605d-7c24-4a1e-b79d-a596ef2dda28
-- title:
--   Indef Link2: forget
-- statement:
--   The Indef Link2 construction uses the forget property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L136-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L136-L142

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefSide
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_IndefUse
import Definitions.Def_Formalism_LocalToGlobal_IndefiniteForms_PairingConditionOfInverseMatrixIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder InnerProductSpace
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Indef
open Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem Formalism.L2.Indef.IndefLink2.forget {Ix : ℝ → Type} {F : ∀ x, Ix x → IndefFace2} {CH : ℝ}
    {Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop}
    (h : IndefLink2 Ix F CH Q) : IndefLink Ix (fun x i => (F x i).toIndefFace) CH Q := by sorry
