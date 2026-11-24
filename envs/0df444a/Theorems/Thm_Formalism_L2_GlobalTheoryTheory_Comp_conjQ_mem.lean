-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_Comp_conjQ_mem
-- name    : Formalism.L2.GlobalTheoryTheory.Comp.conjQ_mem
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T08:35:39.364884+00:00
-- url     : https://prove2.me/theorems/7e333b5e-b90c-4bfe-8c91-a936cd7989b1
-- title:
--   Comp: conj Q mem
-- statement:
--   The Comp construction uses the conj Q mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ExistsUnitaryOneDetEq.lean#L88-L131
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/ExistsUnitaryOneDetEq.lean#L88-L131

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

theorem Formalism.L2.GlobalTheoryTheory.Comp.conjQ_mem (σ : E →ₐ[F] E) (J : Matrix n n E) (Q : Matrix m n E) (Q' : Matrix n m E) (h1 : Q * Q' = 1)
    (h2 : Q' * Q = 1) (hQ : cT (σ : E →+* E) Q * (1 : Matrix m m E) * Q = J) (g : GL n 𝒜)
    (hg : g ∈ UPts σ J (FiniteAdeleRing (𝓞 F) F)) :
    conjQ Q Q' h1 h2 g ∈ UPts σ (1 : Matrix m m E) (FiniteAdeleRing (𝓞 F) F) := by sorry
