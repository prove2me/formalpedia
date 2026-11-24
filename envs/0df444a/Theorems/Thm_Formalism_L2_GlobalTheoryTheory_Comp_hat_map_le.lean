-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hat_map_le
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.hat_map_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:55.65534+00:00
-- url     : https://prove2.me/theorems/57f122bb-4ba2-47ae-9e75-e88641e0963d
-- title:
--   Comp: hat map le
-- statement:
--   The Comp construction uses the hat map le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/MemHatMapGlob.lean#L36-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/MemHatMapGlob.lean#L36-L48

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

theorem Formalism.L2.GlobalTheoryTheory.Comp.hat_map_le (Q : Matrix m n E) (Λ : Submodule (𝓞 E) (n → E)) (u : n → 𝒜) (hu : u ∈ hat F Λ) :
    (Q.map ιA) *ᵥ u ∈ hat F (mapQ Q Λ) := by sorry
