-- Prove2me | Theorems.Thm_Formalism_UG_P_csScale_glob
-- name    : Formalism.UG.P.csScale_glob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:37:37.657877+00:00
-- url     : https://prove2.me/theorems/eb36f4c7-3da8-4995-a52e-e40ed14d1bce
-- title:
--   P: cs Scale glob
-- statement:
--   The P construction uses the cs Scale glob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L164-L180
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L164-L180

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

theorem Formalism.UG.P.csScale_glob (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ)
    (hm : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) * hform (σ : E →+* E) J x y))
    (g : GL n 𝒜) (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) {x y : n → E}
    (hx : x ∈ CS.globLat g Λ) (hy : y ∈ CS.globLat g Λ) :
    ιA ((m : E) * hform (σ : E →+* E) J x y) ∈ 𝒮 := by sorry
