-- Prove2me | Theorems.Thm_Formalism_UG_P_isCommensurated_integral_unitary_of_unramified
-- name    : Formalism.UG.P.isCommensurated_integral_unitary_of_unramified
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:26:41.196725+00:00
-- url     : https://prove2.me/theorems/07fcbee9-097e-408a-b38d-687f751bb903
-- title:
--   P: is Commensurated integral unitary of unramified
-- statement:
--   The P construction uses the is Commensurated integral unitary of unramified property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeA.lean#L22-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/FSatakeA.lean#L22-L82

import Definitions.Def_Formalism_SatakeDualWeyl_StatementF
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_GlintPrincRelIndexNeZero
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_FSatakeA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.UG
noncomputable section
open Formalism Formalism.UG Formalism.UG.P
variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

theorem Formalism.UG.P.isCommensurated_integral_unitary_of_unramified {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (n : ℕ) :
    IsCommensurated (KU σ n) := by sorry
