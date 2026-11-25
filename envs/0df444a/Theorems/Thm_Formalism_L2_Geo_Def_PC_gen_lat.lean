-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_PC_gen_lat
-- name    : Formalism.L2.Geo.Def.PC.gen_lat
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:45:36.310179+00:00
-- url     : https://prove2.me/theorems/0fce187d-01cf-441c-b7fd-9f526056cc97
-- title:
--   PC: gen lat
-- statement:
--   The PC construction uses the gen lat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PClassE.lean#L173-L205
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PClassE.lean#L173-L205

import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassD
import Definitions.Def_Formalism_LocalToGlobal_LatticeGeometry_GeometryDefinitions_PClassE
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix TensorProduct NumberField IsDedekindDomain Formalism.UG Formalism.UG.P
open Formalism Formalism.L2 Formalism.L2.Geo Formalism.L2.Geo.Def Formalism.L2.Geo.Def.PC
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {n : Type} [Fintype n] [DecidableEq n]
local notation "𝔸" => FiniteAdeleRing (𝓞 F) F
local notation "𝒜" => E ⊗[F] FiniteAdeleRing (𝓞 F) F
local notation "𝒮" => tensInt (F := F) (FiniteAdeleRing (𝓞 F) F) (intOE E) (intAd F)

theorem Formalism.L2.Geo.Def.PC.gen_lat (Λ : Submodule (𝓞 E) (n → E)) {p : ℕ} (w : Fin p → Λ)
    (hw : Submodule.span (𝓞 E) (Set.range w) = ⊤) (y : n → 𝒜) (hy : y ∈ latA (F := F) Λ) :
    ∃ s : Fin p → 𝒮, y = ∑ l, s l • (fun i => inclE (F := F) 𝔸 ((w l : n → E) i)) := by sorry
