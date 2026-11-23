-- Prove2me | Theorems.Thm_Formalism_ne_ofReal_of_lt_re
-- name    : Formalism.ne_ofReal_of_lt_re
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:08:02.141456+00:00
-- url     : https://prove2.me/theorems/2be8a35f-ec3c-42d6-a5d7-db4734f976aa
-- title:
--   Formalism: ne of Real of lt re
-- statement:
--   The Formalism construction uses the ne of Real of lt re property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/OfRealNeOfRealOfLt.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/OfRealNeOfRealOfLt.lean#L20-L23

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

theorem Formalism.ne_ofReal_of_lt_re {s : ℂ} {a : ℝ} (h : a < s.re) : s ≠ (a : ℂ) := by sorry
