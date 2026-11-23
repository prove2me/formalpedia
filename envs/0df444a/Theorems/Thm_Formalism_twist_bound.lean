-- Prove2me | Theorems.Thm_Formalism_twist_bound
-- name    : Formalism.twist_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T02:19:40.770041+00:00
-- url     : https://prove2.me/theorems/e5746aca-2a06-4bfc-991f-713f49e3350e
-- title:
--   Formalism: twist bound
-- statement:
--   The Formalism construction uses the twist bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L20-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/MeasurableGchi.lean#L20-L24

import Definitions.Def_Formalism_DefsOC
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
import Definitions.Def_Formalism_ZetaNonvanishing_MeasurableGchi
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
open ArithmeticFunction

theorem Formalism.twist_bound {N : ℕ} (χ : DirichletCharacter ℂ N) :
    ∀ n : ℕ, |Λ n * (χ n).re| ≤ 1 * Λ n := by sorry
