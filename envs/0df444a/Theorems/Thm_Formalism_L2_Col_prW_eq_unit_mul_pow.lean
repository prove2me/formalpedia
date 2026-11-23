-- Prove2me | Theorems.Thm_Formalism_L2_Col_prW_eq_unit_mul_pow
-- name    : Formalism.L2.Col.prW_eq_unit_mul_pow
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:07:35.204546+00:00
-- url     : https://prove2.me/theorems/4fcb979c-c96b-4b11-b8a9-2d6fa0659bb5
-- title:
--   Col: pr W eq unit mul pow
-- statement:
--   The Col construction uses the pr W eq unit mul pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L300-L316
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L300-L316

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

theorem Formalism.L2.Col.prW_eq_unit_mul_pow (w : HeightOneSpectrum (𝓞 K)) {ϖ : Ow w} (hϖ : Irreducible ϖ) :
    ∃ u : (Ow w)ˣ, ((prW w : ℕ) : Ow w) = u * ϖ ^ eW w := by sorry
