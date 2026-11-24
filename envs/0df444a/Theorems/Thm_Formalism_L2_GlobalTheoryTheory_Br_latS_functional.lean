-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Br_latS_functional
-- name    : Formalism.L2.GlobalTheoryTheory.Br.latS_functional
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:10.979397+00:00
-- url     : https://prove2.me/theorems/9082e598-b33a-455c-9765-bf021f459c33
-- title:
--   Br: lat S functional
-- statement:
--   The Br construction uses the lat S functional property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/BlockActions/FiniteAdeleRingNontrivial.lean#L33-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/BlockActions/FiniteAdeleRingNontrivial.lean#L33-L72

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

theorem Formalism.L2.GlobalTheoryTheory.Br.latS_functional (Λ : Submodule (𝓞 E) (Fin n → E)) (f : Module.Dual E (Fin n → E))
    (hf : ∀ y ∈ Λ, f y = 0) (x : Fin n → E)
    (hx : (fun i => ι (x i)) ∈ latS (F := F) (FiniteAdeleRing (𝓞 F) F) 𝒮 Λ) : f x = 0 := by sorry
