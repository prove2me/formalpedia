-- Prove2me | Theorems.Thm_Formalism_L2_FormalSeriesBounds_RF_minorMonomial_mem_ZP
-- name    : Formalism.L2.FormalSeriesBounds.RF.minorMonomial_mem_ZP
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T00:46:29.371685+00:00
-- url     : https://prove2.me/theorems/af285abe-a5ff-46fa-9f14-f2cf2fead3fb
-- title:
--   RF: minor Monomial mem ZP
-- statement:
--   The RF construction uses the minor Monomial mem ZP property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L45-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/CharacterGerms/NormOneIntegral.lean#L45-L47

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_BlockMembershipNormOne
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_NormOneIntegral
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
open Formalism.IncomingBounds Formalism.L2.Pj
variable {C : Type} [Field C]

theorem Formalism.L2.FormalSeriesBounds.RF.minorMonomial_mem_ZP (N N' : ℕ) (e : ℕ → ℕ) : monP C N N' e ∈ ZP C (Fin N × Fin N') := by sorry
