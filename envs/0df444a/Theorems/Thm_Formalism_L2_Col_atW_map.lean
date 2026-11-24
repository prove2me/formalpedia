-- Prove2me | Theorems.Thm_Formalism_L2_Col_atW_map
-- name    : Formalism.L2.Col.atW_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:54.729796+00:00
-- url     : https://prove2.me/theorems/7b79157a-b858-465c-b3f5-488b4af03a8a
-- title:
--   Col: at W map
-- statement:
--   The Col construction uses the at W map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L162-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L162-L168

import Mathlib
import Definitions.Def_Formalism_HermitianLattices_StatementLat
import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_LocalToGlobal_Columns_AlgebraMapMemMaximalIdealPowIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Col
variable {K : Type} [Field K] [NumberField K]
variable {V : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

theorem Formalism.L2.Col.atW_map {V' : Type} [AddCommGroup V'] [Module K V'] [Module (𝓞 K) V']
    [IsScalarTower (𝓞 K) K V'] (w : HeightOneSpectrum (𝓞 K)) (f : V →ₗ[K] V')
    (L : Submodule (𝓞 K) V) :
    atW w (L.map (f.restrictScalars (𝓞 K))) = (atW w L).map (f.restrictScalars (Ow w)) := by sorry
