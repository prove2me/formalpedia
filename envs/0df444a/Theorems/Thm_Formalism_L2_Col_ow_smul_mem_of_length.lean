-- Prove2me | Theorems.Thm_Formalism_L2_Col_ow_smul_mem_of_length
-- name    : Formalism.L2.Col.ow_smul_mem_of_length
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:27.886472+00:00
-- url     : https://prove2.me/theorems/cbe90b1a-cef9-4773-bc4f-8c5e861b717b
-- title:
--   Col: ow smul mem of length
-- statement:
--   The Col construction uses the ow smul mem of length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L432-L446
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L432-L446

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
variable (w : HeightOneSpectrum (𝓞 K)) (Q : Type) [AddCommGroup Q] [Module (Ow w) Q] [Module (𝓞 K) Q]
  [IsScalarTower (𝓞 K) (Ow w) Q]

theorem Formalism.L2.Col.ow_smul_mem_of_length (hQ : Module.length (Ow w) Q ≠ ⊤) (N : Submodule (𝓞 K) Q) (r : Ow w)
    {x : Q} (hx : x ∈ N) : r • x ∈ N := by sorry
