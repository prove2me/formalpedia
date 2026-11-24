-- Prove2me | Theorems.Thm_Formalism_deriv_Pfun_of_ne
-- name    : Formalism.deriv_Pfun_of_ne
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T10:44:25.804633+00:00
-- url     : https://prove2.me/theorems/789932c5-415c-49ed-8dd8-670bb1b089e2
-- title:
--   Formalism: deriv Pfun of ne
-- statement:
--   The Formalism construction uses the deriv Pfun of ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L28-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/ZetaNonvanishing/Assembly.lean#L28-L42

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

theorem Formalism.deriv_Pfun_of_ne {s : ℂ} (hs : s ≠ 1) :
    deriv (Pfun χ) s = riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * deriv riemannZeta s * DirichletCharacter.LFunction χ s
      + (s - 1) * riemannZeta s * deriv (DirichletCharacter.LFunction χ) s := by sorry
