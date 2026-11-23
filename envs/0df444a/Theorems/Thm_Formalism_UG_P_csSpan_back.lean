-- Prove2me | Theorems.Thm_Formalism_UG_P_csSpan_back
-- name    : Formalism.UG.P.csSpan_back
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:50:13.850013+00:00
-- url     : https://prove2.me/theorems/2fea33fa-e7d9-4339-8985-6565f999d7fa
-- title:
--   P: cs Span back
-- statement:
--   The P construction uses the cs Span back property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsSpan.lean#L64-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsSpan.lean#L64-L150

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

theorem Formalism.UG.P.csSpan_back (hA : Formalism.UG.CS.IntAdApprox) (Λ : Submodule (𝓞 E) (n → E))
    (hfin : Module.Finite (𝓞 E) Λ) (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤)
    (g : GL n 𝒜) (u : n → 𝒜)
    (hu : ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) :
    u ∈ Submodule.span 𝒮 ((fun x : n → E => fun i => ι (x i)) ''
      (Formalism.UG.CS.globLat g Λ : Set (n → E))) := by sorry
