-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_glob_glob_inv
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.glob_glob_inv
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T22:48:24.388801+00:00
-- url     : https://prove2.me/theorems/698926f7-ce28-4bcd-be18-b73334ea6a9e
-- title:
--   Comp: glob glob inv
-- statement:
--   The Comp construction uses the glob glob inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/EqGlobOfHat.lean#L57-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/EqGlobOfHat.lean#L57-L59

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

theorem Formalism.L2.GlobalTheoryTheory.Comp.glob_glob_inv {Λ : Submodule (𝓞 E) (n → E)} (h : IsLat Λ) (g : GL n 𝒜) :
    globLat g⁻¹ (globLat g Λ) = Λ := by sorry
