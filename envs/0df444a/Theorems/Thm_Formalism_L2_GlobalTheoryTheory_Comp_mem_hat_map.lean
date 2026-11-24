-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_mem_hat_map
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_map
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:26.613081+00:00
-- url     : https://prove2.me/theorems/8a7bd37e-fee2-4a09-8d5c-ffca388affd6
-- title:
--   Comp: mem hat map
-- statement:
--   The Comp construction uses the mem hat map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/MemHatMapGlob.lean#L54-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/MemHatMapGlob.lean#L54-L62

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

theorem Formalism.L2.GlobalTheoryTheory.Comp.mem_hat_map (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1) (h2 : Q' * Q = 1)
    (Λ : Submodule (𝓞 E) (n → E)) (v : m → 𝒜) : v ∈ hat F (mapQ Q Λ) ↔ (Q'.map ιA) *ᵥ v ∈ hat F Λ := by sorry
