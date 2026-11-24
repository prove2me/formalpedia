-- Prove2me | Theorems.Thm_Formalism_L2_Col_exists_pow_smul_eq_zero
-- name    : Formalism.L2.Col.exists_pow_smul_eq_zero
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:50:17.885587+00:00
-- url     : https://prove2.me/theorems/3cc06d53-5b86-4d91-936e-9e640d34e1dc
-- title:
--   Col: exists pow smul eq zero
-- statement:
--   The Col construction uses the exists pow smul eq zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L413-L430
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/AlgebraMapMemMaximalIdealPowIff.lean#L413-L430

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

theorem Formalism.L2.Col.exists_pow_smul_eq_zero (hQ : Module.length (Ow w) Q ≠ ⊤) (x : Q) :
    ∃ n : ℕ, ∀ c ∈ w.asIdeal ^ n, c • x = 0 := by sorry
