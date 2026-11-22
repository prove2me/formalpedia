-- Prove2me | Theorems.Thm_Formalism_UG_P_csDual_hform_incl
-- name    : Formalism.UG.P.csDual_hform_incl
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-22T23:10:52.653731+00:00
-- url     : https://prove2.me/theorems/95cfe837-dc45-48dc-9fd9-bc462f7e056e
-- title:
--   P: cs Dual hform incl
-- statement:
--   The P construction uses the cs Dual hform incl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsDual.lean#L79-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsDual.lean#L79-L82

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_Bridge
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
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
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.UG.P.csDual_hform_incl (σ : E →ₐ[F] E) (J : Matrix n n E) (y x : n → E) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ι) (fun i => ι (y i)) (fun i => ι (x i)) =
      ι (hform (σ : E →+* E) J y x) := by sorry
