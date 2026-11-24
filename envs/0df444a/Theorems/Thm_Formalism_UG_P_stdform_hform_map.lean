-- Prove2me | Theorems.Thm_Formalism_UG_P_stdform_hform_map
-- name    : Formalism.UG.P.stdform_hform_map
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:36:00.850123+00:00
-- url     : https://prove2.me/theorems/c31299af-2f9e-49ba-bdb2-af7c63b7b08c
-- title:
--   P: stdform hform map
-- statement:
--   The P construction uses the stdform hform map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stdform.lean#L141-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/Stdform.lean#L141-L145

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
variable {n : Type} [Fintype n] [DecidableEq n] {F E : Type} [Field F] [Field E] [Algebra F E]

theorem Formalism.UG.P.stdform_hform_map (σ : E →ₐ[F] E) (τ : E →+* ℂ)
    (hσ : τ.comp (σ : E →+* E) = (starRingEnd ℂ).comp τ) (J : Matrix n n E) (x : n → E) :
    τ (hform (σ : E →+* E) J x x) =
      ∑ i, ∑ j, starRingEnd ℂ (τ (x i)) * (J.map τ) i j * τ (x j) := by sorry
