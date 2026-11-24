-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Herm4_form_repr
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.form_repr
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T07:57:44.7425+00:00
-- url     : https://prove2.me/theorems/a653895d-67af-4fe6-8dcb-0fcac33e89ae
-- title:
--   Herm4: form repr
-- statement:
--   The Herm4 construction uses the form repr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L136-L148
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PFourSq.lean#L136-L148

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

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Herm4.form_repr (H : Herm4 c h) {n : Type} [Fintype n] [DecidableEq n] (b : Basis n K V)
    (hb : ∀ i j, i ≠ j → h (b i) (b j) = 0) (u v : V) :
    h u v = ∑ i, h (b i) (b i) * (b.repr u i * c (b.repr v i)) := by sorry
