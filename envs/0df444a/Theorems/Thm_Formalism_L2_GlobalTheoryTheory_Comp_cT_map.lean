-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_cT_map
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.cT_map
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:23.006027+00:00
-- url     : https://prove2.me/theorems/3850762b-5f6f-4499-811b-0a808e7433b7
-- title:
--   Comp: c T map
-- statement:
--   The Comp construction uses the c T map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ExistsUnitaryOneDetEq.lean#L76-L86
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ExistsUnitaryOneDetEq.lean#L76-L86

import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_MemHatMapGlob
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_ExistsUnitaryOneDetEq
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

theorem Formalism.L2.GlobalTheoryTheory.Comp.cT_map (σ : E →ₐ[F] E) {p q : Type} (Q : Matrix p q E) :
    cT (sigR σ (FiniteAdeleRing (𝓞 F) F)) (Q.map ιA) = (cT (σ : E →+* E) Q).map ιA := by sorry
