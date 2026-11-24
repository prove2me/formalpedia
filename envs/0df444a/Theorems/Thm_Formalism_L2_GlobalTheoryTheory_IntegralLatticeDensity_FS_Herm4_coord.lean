-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_coord
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.coord
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:56.87592+00:00
-- url     : https://prove2.me/theorems/ae266658-0f07-4b4b-9755-a1a1d4cbeca6
-- title:
--   Herm4: coord
-- statement:
--   The Herm4 construction uses the coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L220-L222
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L220-L222

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.coord (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (v : V) (i : n) : h v (b i) = b.repr v i * h (b i) (b i) := by sorry
