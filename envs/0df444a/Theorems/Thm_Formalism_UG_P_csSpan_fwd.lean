-- Prove2me | Theorems.Thm_Formalism_UG_P_csSpan_fwd
-- name    : Formalism.UG.P.csSpan_fwd
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T10:31:56.930156+00:00
-- url     : https://prove2.me/theorems/1d0819f1-e8c5-4c41-89a5-642792f879a2
-- title:
--   P: cs Span fwd
-- statement:
--   The P construction uses the cs Span fwd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsSpan.lean#L50-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsSpan.lean#L50-L62

import Definitions.Def_Formalism_SatakeDualWeyl_DefsCS
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_AdelstabL
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
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

theorem Formalism.UG.P.csSpan_fwd (Λ : Submodule (𝓞 E) (n → E)) (g : GL n 𝒜) (u : n → 𝒜)
    (hu : u ∈ Submodule.span 𝒮 ((fun x : n → E => fun i => ι (x i)) ''
      (Formalism.UG.CS.globLat g Λ : Set (n → E)))) :
    ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ := by sorry
