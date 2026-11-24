-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Br_latS_mono_fin
-- name    : Formalism.L2.GlobalTheoryTheory.Br.latS_mono_fin
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:28.828131+00:00
-- url     : https://prove2.me/theorems/d68b3f80-ea51-45ac-a09d-7548db7490d2
-- title:
--   Br: lat S mono fin
-- statement:
--   The Br construction uses the lat S mono fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/BlockActions/FiniteAdeleRingNontrivial.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/BlockActions/FiniteAdeleRingNontrivial.lean#L29-L31

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_LatSOfMem
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_InclusionInjective
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_BlockActions_FiniteAdeleRingNontrivial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Br
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ι" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.L2.GlobalTheoryTheory.Br.latS_mono_fin {Λ Λ' : Submodule (𝓞 E) (Fin n → E)} (h : Λ ≤ Λ') :
    latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ ≤ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ' := by sorry
