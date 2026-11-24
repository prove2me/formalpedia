-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_ortho_fam
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.ortho_fam
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:51.849169+00:00
-- url     : https://prove2.me/theorems/67f3d2ef-3944-4fe5-adaa-b8f75c91a53d
-- title:
--   Herm4: ortho fam
-- statement:
--   The Herm4 construction uses the ortho fam property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L58-L91
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L58-L91

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.ortho_fam (H : Herm4 c h) (m : ℕ) (hm : m ≤ finrank K V) :
    ∃ v : Fin m → V, (∀ i, v i ≠ 0) ∧ ∀ i j, i ≠ j → h (v i) (v j) = 0 := by sorry
