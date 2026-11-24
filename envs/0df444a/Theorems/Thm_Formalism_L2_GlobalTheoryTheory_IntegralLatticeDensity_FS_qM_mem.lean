-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_qM_mem
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.qM_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:58:05.459006+00:00
-- url     : https://prove2.me/theorems/80fb7261-95b0-4533-ab95-8cdc2ffeaa15
-- title:
--   FS: q M mem
-- statement:
--   The FS construction uses the q M mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L228-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L228-L230

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PUnitBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Module
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS
variable {K : Type} [Field K] [CharZero K] {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {c : K →+* K} {h : V → V → K} {O : Subring K} {L : AddSubgroup V} {p : ℕ}

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.qM_mem (O : Subring K) {p q r s : K} (hp : p ∈ O) (hq : q ∈ O) (hr : r ∈ O) (hs : s ∈ O) (β a : Fin 4) :
    qM p q r s β a ∈ O := by sorry
