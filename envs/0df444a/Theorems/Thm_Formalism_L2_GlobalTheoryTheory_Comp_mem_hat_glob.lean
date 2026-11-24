-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_hat_glob
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_glob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T01:41:53.419491+00:00
-- url     : https://prove2.me/theorems/8ecb07fc-1d95-4de2-bcd3-f2a8dfa5d71f
-- title:
--   Comp: mem hat glob
-- statement:
--   The Comp construction uses the mem hat glob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/EqGlobOfHat.lean#L42-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/EqGlobOfHat.lean#L42-L44

import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsGlob
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsSpan
import Definitions.Def_Formalism_SatakeDualWeyl_AdelicIwasawaHecke_CsDual
import Definitions.Def_Formalism_LocalRingCardinality_DataLevel
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
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
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.Comp
open Formalism.UG Formalism.UG.CS Formalism.UG.P Formalism.BasicNotions
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_glob {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g : GL n 𝒜) (u : n → 𝒜) :
    u ∈ hat F (globLat g Λ) ↔ ((g⁻¹ : GL n 𝒜) : Matrix n n 𝒜) *ᵥ u ∈ hat F Λ := by sorry
