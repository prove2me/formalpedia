-- Prove2me | Theorems.Thm_Formalism_UG_P_csScale_latS
-- name    : Formalism.UG.P.csScale_latS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:11:41.793822+00:00
-- url     : https://prove2.me/theorems/910b2846-107f-48a7-8fb0-e452aeb9a8c3
-- title:
--   P: cs Scale lat S
-- statement:
--   The P construction uses the cs Scale lat S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L127-L152
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsScale.lean#L127-L152

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

theorem Formalism.UG.P.csScale_latS (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E)) (m : ℤ)
    (hm : ∀ x ∈ Λ, ∀ y ∈ Λ, IsIntegral ℤ ((m : E) * hform (σ : E →+* E) J x y))
    {u w : n → 𝒜} (hu : u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ)
    (hw : w ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
    ιA (m : E) * hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ιA) u w ∈ 𝒮 := by sorry
