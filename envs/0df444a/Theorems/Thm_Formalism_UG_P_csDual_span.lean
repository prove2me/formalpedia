-- Prove2me | Theorems.Thm_Formalism_UG_P_csDual_span
-- name    : Formalism.UG.P.csDual_span
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:58:30.792711+00:00
-- url     : https://prove2.me/theorems/d8c4f979-2213-453f-891e-a16c515d4f38
-- title:
--   P: cs Dual span
-- statement:
--   The P construction uses the cs Dual span property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsDual.lean#L84-L99
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SatakeDualWeyl/AdelicIwasawaHecke/CsDual.lean#L84-L99

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

theorem Formalism.UG.P.csDual_span (σ : E →ₐ[F] E) (J : Matrix n n E) (M : Submodule (𝓞 E) (n → E)) (x : n → E)
    (hx : ∀ y ∈ M, hform (σ : E →+* E) J y x ∈ (algebraMap (𝓞 E) E).range)
    (u : n → 𝒜) (hu : u ∈ Submodule.span 𝒮 ((fun y : n → E => fun i => ι (y i)) '' (M : Set (n → E)))) :
    hform (sigR σ (FiniteAdeleRing (𝓞 F) F)) (J.map ι) u (fun i => ι (x i)) ∈ 𝒮 := by sorry
