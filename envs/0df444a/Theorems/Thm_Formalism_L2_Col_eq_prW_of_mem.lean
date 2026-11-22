-- Prove2me | Theorems.Thm_Formalism_L2_Col_eq_prW_of_mem
-- name    : Formalism.L2.Col.eq_prW_of_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:46:07.120679+00:00
-- url     : https://prove2.me/theorems/33e583c2-8211-409b-85f3-cb6526c01834
-- title:
--   Col: eq pr W of mem
-- statement:
--   The Col construction uses the eq pr W of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L284-L290
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L284-L290

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

theorem Formalism.L2.Col.eq_prW_of_mem (w : HeightOneSpectrum (𝓞 K)) {q : ℕ} (hq : q.Prime)
    (h : ((q : ℕ) : 𝓞 K) ∈ w.asIdeal) : q = prW w := by sorry
