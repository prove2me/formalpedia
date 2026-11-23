-- Prove2me | Theorems.Thm_Formalism_L2_Indef_IndefLink2_toR
-- name    : Formalism.L2.Indef.IndefLink2.toR
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:19:49.870421+00:00
-- url     : https://prove2.me/theorems/b1421f3c-eeb3-4842-918e-eda688552e99
-- title:
--   Indef Link2: to R
-- statement:
--   The Indef Link2 construction uses the to R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L307-L313
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/IndefiniteForms/PairingConditionOfInverseMatrixIdentity.lean#L307-L313

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

theorem Formalism.L2.Indef.IndefLink2.toR {Ix : ℝ → Type} {F : ∀ x, Ix x → IndefFace2} {CH : ℝ}
    {Q : ∀ x (i : Ix x), ℝ → DefSub (F x i).A → (HeightOneSpectrum (𝓞 (F x i).K) → (F x i).Bs.Tup) → Prop}
    (h : IndefLink2 Ix F CH Q) : IndefLinkR Ix F CH Q := by sorry
