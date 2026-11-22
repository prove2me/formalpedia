-- Prove2me | Theorems.Thm_Formalism_Pfun_eq_of_ne
-- name    : Formalism.Pfun_eq_of_ne
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T16:58:25.555722+00:00
-- url     : https://prove2.me/theorems/6e7e2546-0db8-4a9f-924b-8780b775172e
-- title:
--   Formalism: Pfun eq of ne
-- statement:
--   The Formalism construction uses the Pfun eq of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L13-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L13-L15

import Definitions.Def_Formalism_ZetaRealNonvanish
import Definitions.Def_Formalism_ZetaNonvanishing_Assembly
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
variable {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)

theorem Formalism.Pfun_eq_of_ne {s : ℂ} (hs : s ≠ 1) :
    Pfun χ s = (s - 1) * riemannZeta s * DirichletCharacter.LFunction χ s := by sorry
