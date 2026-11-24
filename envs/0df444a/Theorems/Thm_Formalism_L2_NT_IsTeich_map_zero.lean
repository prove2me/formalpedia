-- Prove2me | Theorems.Thm_Formalism_L2_NT_IsTeich_map_zero
-- name    : Formalism.L2.NT.IsTeich.map_zero
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T17:55:23.198313+00:00
-- url     : https://prove2.me/theorems/2fe0f435-27ff-4944-aeea-c8c931d08d87
-- title:
--   Is Teich: map zero
-- statement:
--   The Is Teich construction uses the map zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L77-L85
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/NormalizedHeckeFactors/TypesDefs.lean#L77-L85

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_UnitaryNorms_RealCyclotomicTwoPower
import Definitions.Def_Formalism_CyclotomicNorms_StatementT
import Definitions.Def_Formalism_LocalToGlobal_NormalizedHeckeFactors_TypesDefs
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain Polynomial
open Formalism Formalism.L2 Formalism.L2.NT
open Formalism.L2.Host

theorem Formalism.L2.NT.IsTeich.map_zero {Ω : Type} [Field Ω] {A : ValuationSubring Ω} {p : ℕ} [Fact p.Prime]
    {κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar p} {t : Formalism.CyclotomicNorms.Fbar p →* Ω} (h : IsTeich A κ t) : t 0 = 0 := by sorry
