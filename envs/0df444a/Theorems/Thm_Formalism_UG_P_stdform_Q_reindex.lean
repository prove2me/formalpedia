-- Prove2me | Theorems.Thm_Formalism_UG_P_stdform_Q_reindex
-- name    : Formalism.UG.P.stdform_Q_reindex
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T10:36:44.869487+00:00
-- url     : https://prove2.me/theorems/8fe5f14d-7a23-4429-8a66-60b75468a359
-- title:
--   P: stdform Q reindex
-- statement:
--   The P construction uses the stdform Q reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stdform.lean#L31-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stdform.lean#L31-L37

import Definitions.Def_Formalism_SatakeDualWeyl_StatementC
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureExists
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_SignatureConjugationInvariant
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Stdform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {n : Type} [Fintype n] [DecidableEq n]

theorem Formalism.UG.P.stdform_Q_reindex {m : Type} [Fintype m] [DecidableEq m] (M : Matrix n n ℂ) (e : n ≃ m)
    (y : n → ℂ) : stdformQ (M.reindex e e) (fun k => y (e.symm k)) = stdformQ M y := by sorry
