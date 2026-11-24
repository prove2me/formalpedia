-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_exists_unitary_one_det_eq
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.exists_unitary_one_det_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:29.07097+00:00
-- url     : https://prove2.me/theorems/7fd0a85a-e090-4d2e-9734-3556ec6e81d6
-- title:
--   Comp: exists unitary one det eq
-- statement:
--   The Comp construction uses the exists unitary one det eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ExistsUnitaryOneDetEq.lean#L133-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ExistsUnitaryOneDetEq.lean#L133-L168

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

theorem Formalism.L2.GlobalTheoryTheory.Comp.exists_unitary_one_det_eq (σ : E →ₐ[F] E) (G : GL m 𝒜) (hG : G ∈ UPts σ (1 : Matrix m m E) (FiniteAdeleRing (𝓞 F) F)) :
    ∃ x : GL (Fin 1) 𝒜, x ∈ UPts σ (1 : Matrix (Fin 1) (Fin 1) E) (FiniteAdeleRing (𝓞 F) F) ∧
      Matrix.GeneralLinearGroup.det x = Matrix.GeneralLinearGroup.det G := by sorry
