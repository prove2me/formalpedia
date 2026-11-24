-- Prove2me | Theorems.Thm_Formalism_L2_Col_mem_scalW_iff
-- name    : Formalism.L2.Col.mem_scalW_iff
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:26.607541+00:00
-- url     : https://prove2.me/theorems/bdd93985-ae14-4800-8579-0d0a70876b60
-- title:
--   Col: mem scal W iff
-- statement:
--   The Col construction uses the mem scal W iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L181-L182
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L181-L182

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

theorem Formalism.L2.Col.mem_scalW_iff {w : HeightOneSpectrum (𝓞 K)} {c : K} {L : Submodule (𝓞 K) V} {x : V} :
    x ∈ scalW w c L ↔ ∃ y ∈ atW w L, c • y = x := by sorry
