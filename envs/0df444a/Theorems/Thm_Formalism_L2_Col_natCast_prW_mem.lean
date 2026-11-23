-- Prove2me | Theorems.Thm_Formalism_L2_Col_natCast_prW_mem
-- name    : Formalism.L2.Col.natCast_prW_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:47.92398+00:00
-- url     : https://prove2.me/theorems/1fdb9ee2-dabe-4087-b98e-5360d52b865e
-- title:
--   Col: nat Cast pr W mem
-- statement:
--   The Col construction uses the nat Cast pr W mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L279-L282
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L279-L282

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

theorem Formalism.L2.Col.natCast_prW_mem (w : HeightOneSpectrum (𝓞 K)) : ((prW w : ℕ) : 𝓞 K) ∈ w.asIdeal := by sorry
