-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_mapQ
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.mem_mapQ
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:46.964445+00:00
-- url     : https://prove2.me/theorems/00861254-0be3-4a31-a989-e8e6943e60ac
-- title:
--   Comp: mem map Q
-- statement:
--   The Comp construction uses the mem map Q property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/MemHatMapGlob.lean#L21-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/MemHatMapGlob.lean#L21-L22

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_EqGlobOfHat
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
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
  {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)
local notation "ιA" => inclE (F := F) (E := E) (FiniteAdeleRing (𝓞 F) F)

theorem Formalism.L2.GlobalTheoryTheory.Comp.mem_mapQ (Q : Matrix m n E) (Λ : Submodule (𝓞 E) (n → E)) (y : m → E) :
    y ∈ mapQ Q Λ ↔ ∃ x ∈ Λ, Q *ᵥ x = y := by sorry
