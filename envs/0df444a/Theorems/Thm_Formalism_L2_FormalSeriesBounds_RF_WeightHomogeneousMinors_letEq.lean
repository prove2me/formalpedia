-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_WeightHomogeneousMinors_letEq
-- name    : Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.letEq
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T00:52:33.140992+00:00
-- url     : https://prove2.me/theorems/196a9ffc-6239-4bd0-946b-5d6a1cf82b20
-- title:
--   Weight Homogeneous Minors: let Eq
-- statement:
--   The Weight Homogeneous Minors construction uses the let Eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L108-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneRowDegrees.lean#L108-L116

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneRowDegrees
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Classical
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.RF
open Formalism.IncomingBounds Formalism.L2.Pj MvPolynomial
open Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors
variable {T : Type} (r : T → ℕ) (n : ℕ)
variable {r n}

theorem Formalism.L2.FormalSeriesBounds.RF.WeightHomogeneousMinors.letEq {τ1 τ2 : T} {c1 : Fin (r τ1)} {c2 : Fin (r τ2)} {b1 b2 : Fin n} :
    ((⟨τ1, (c1, b1)⟩ : Letter T r n) = ⟨τ2, (c2, b2)⟩) ↔ ((⟨τ1, c1⟩ : Σ σ, Fin (r σ)) = ⟨τ2, c2⟩ ∧ b1 = b2) := by sorry
