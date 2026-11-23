-- Prove2me | Theorems.Thm_Formalism_ofReal_ne_ofReal_of_lt
-- name    : Formalism.ofReal_ne_ofReal_of_lt
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:07:57.418057+00:00
-- url     : https://prove2.me/theorems/0b48cf9b-bc58-4410-808a-afa82929251e
-- title:
--   Formalism: of Real ne of Real of lt
-- statement:
--   The Formalism construction uses the of Real ne of Real of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/OfRealNeOfRealOfLt.lean#L14-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/OfRealNeOfRealOfLt.lean#L14-L18

import Definitions.Def_Formalism_ZetaNonvanishing_RiemannZetaOneNeZeroOfRealMemIoo
import Definitions.Def_Formalism_ZetaNonvanishing_OfRealNeOfRealOfLt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex MeasureTheory Set Filter Topology
noncomputable section
open Formalism
variable {ι : Type} [Fintype ι] [DecidableEq ι] {N : ι → ℕ} [∀ i, NeZero (N i)]
  (χ : (i : ι) → DirichletCharacter ℂ (N i)) (w : ι → ℝ)

theorem Formalism.ofReal_ne_ofReal_of_lt {a b : ℝ} (h : a < b) : (b : ℂ) ≠ (a : ℂ) := by sorry
