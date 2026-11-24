-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_hat_map_glob
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_map_glob
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:35.47808+00:00
-- url     : https://prove2.me/theorems/92b997c9-1c76-47b6-bc00-aa9f681a6e3e
-- title:
--   Comp: mem hat map glob
-- statement:
--   The Comp construction uses the mem hat map glob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/MemHatMapGlob.lean#L86-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/MemHatMapGlob.lean#L86-L96

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

theorem Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_map_glob (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1)
    {Λ : Submodule (𝓞 E) (n → E)} (hΛ : IsLat Λ) (g : GL n 𝒜) (v : m → 𝒜) :
    v ∈ hat F (mapQ Q (globLat g Λ)) ↔
      (((conjQ Q Q' h1 h2 g)⁻¹ : GL m 𝒜) : Matrix m m 𝒜) *ᵥ v ∈ hat F (mapQ Q Λ) := by sorry
