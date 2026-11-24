-- Prove2me | Theorems.Thm_Formalism_L2_Col_lenW_eq_length
-- name    : Formalism.L2.Col.lenW_eq_length
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:08:36.306558+00:00
-- url     : https://prove2.me/theorems/c27ea750-2246-4aaf-b2c8-bd0f89d21f94
-- title:
--   Col: len W eq length
-- statement:
--   The Col construction uses the len W eq length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L465-L489
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L465-L489

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

theorem Formalism.L2.Col.lenW_eq_length (w : HeightOneSpectrum (𝓞 K)) (A B : Submodule (𝓞 K) V) :
    lenW w A B = Module.length (𝓞 K) (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A ⧸
      (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal B).comap (Formalism.HermitianLatticesTheory.localization₂ w.asIdeal A).subtype) := by sorry
