-- Prove2me | Theorems.Thm_Formalism_L2_Geo_Def_PC_kstLoc
-- name    : Formalism.L2.Geo.Def.PC.kstLoc
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:45:53.397796+00:00
-- url     : https://prove2.me/theorems/b8b06c50-e856-4e06-9831-474d854feee9
-- title:
--   PC: kst Loc
-- statement:
--   The PC construction uses the kst Loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PClassE.lean#L135-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/LatticeGeometry/GeometryDefinitions/PClassE.lean#L135-L163

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

theorem Formalism.L2.Geo.Def.PC.kstLoc (σ : E →ₐ[F] E) (J : Matrix n n E) (Λ : Submodule (𝓞 E) (n → E))
    (hspan : Submodule.span E (Λ : Set (n → E)) = ⊤) (x : GL n 𝒜) :
    x ∈ levelAfL σ J Λ ↔ x ∈ UPts σ J 𝔸 ∧ ∀ v, bc (prV (E := E) v) x ∈ levelVL σ J v Λ := by sorry
