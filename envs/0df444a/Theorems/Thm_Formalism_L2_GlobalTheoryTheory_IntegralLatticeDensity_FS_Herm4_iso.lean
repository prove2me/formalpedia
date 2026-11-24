-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_iso
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.iso
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:53:56.915801+00:00
-- url     : https://prove2.me/theorems/ce096e94-cb09-4447-a070-65ba39e78764
-- title:
--   Herm4: iso
-- statement:
--   The Herm4 construction uses the iso property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L207-L218
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L207-L218

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL3_PFourSq
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
variable {K : Type} [Field K]
variable {V : Type} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable (c : K →+* K) (h : V → V → K)
variable {c h}

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.iso (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (hn : Fintype.card n = finrank K V) :
    ∃ g : (Fin 4 → V) ≃ₗ[K] (Fin 4 × n → K), ∀ x y, ∑ w, g x w * c (g y w) = ∑ a, h (x a) (y a) := by sorry
