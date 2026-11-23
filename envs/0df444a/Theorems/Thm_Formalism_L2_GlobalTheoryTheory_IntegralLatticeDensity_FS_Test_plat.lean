-- Prove2me | Theorems.Thm_Formalism_L2_GlobalTheoryTheory_IntegralLatticeDensity_FS_Test_plat
-- name    : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test.plat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T04:59:53.582162+00:00
-- url     : https://prove2.me/theorems/560080b1-50ab-4e3b-9079-2ae8a258f436
-- title:
--   Test: plat
-- statement:
--   The Test construction uses the plat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L292-L319
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/GlobalTheory/GL3/PUnitBasis.lean#L292-L319

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
open Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test

theorem Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.FS.Test.plat : PLat (RingHom.id ℚ) (fun x y : ℚ => x * y) (Int.castRingHom ℚ).range (Int.castAddHom ℚ).range 3 := by sorry
