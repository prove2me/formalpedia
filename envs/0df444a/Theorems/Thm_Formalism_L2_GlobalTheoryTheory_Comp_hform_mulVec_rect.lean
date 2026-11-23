-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_hform_mulVec_rect
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:12:37.278841+00:00
-- url     : https://prove2.me/theorems/563aeff7-465a-429b-bc55-86283ced2d81
-- title:
--   Comp: hform mul Vec rect
-- statement:
--   The Comp construction uses the hform mul Vec rect property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ExistsUnitaryOneDetEq.lean#L31-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ExistsUnitaryOneDetEq.lean#L31-L47

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

theorem Formalism.L2.GlobalTheoryTheory.Comp.hform_mulVec_rect {A : Type} [CommRing A] (τ : A →+* A) (J' : Matrix m m A) (Q : Matrix m n A)
    (x y : n → A) : hform τ J' (Q *ᵥ x) (Q *ᵥ y) = hform τ (cT τ Q * J' * Q) x y := by sorry
