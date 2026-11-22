-- Prove2me | Theorems.Thm_Formalism_UG_P_csScale_hform_incl
-- name    : Formalism.UG.P.csScale_hform_incl
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:22.274563+00:00
-- url     : https://prove2.me/theorems/5014f63a-444b-4719-aca5-b8571894fa2e
-- title:
--   P: cs Scale hform incl
-- statement:
--   The P construction uses the cs Scale hform incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L84-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L84-L87

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsScale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain
open Formalism Formalism.UG Formalism.UG.P
open Formalism.UG
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.UG.P.csScale_hform_incl (σ : E →ₐ[F] E) (J : Matrix n n E) (x y : n → E) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) (fun i => ιA (x i)) (fun i => ιA (y i)) =
      ιA (hform (σ : E →+* E) J x y) := by sorry
