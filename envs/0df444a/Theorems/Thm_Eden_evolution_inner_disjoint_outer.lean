-- Prove2me | Theorems.Thm_Eden_evolution_inner_disjoint_outer
-- name    : Eden.evolution_inner_disjoint_outer
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T14:44:47.56738+00:00
-- url     : https://prove2.me/theorems/42b22a26-43e1-4bae-8e9e-cddbd485bace
-- title:
--   Eden: evolution inner disjoint outer
-- statement:
--   The Eden construction uses the evolution inner disjoint outer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L107-L110
-- source:
--   https://github.com/MColbrook/Eden_conjecture/blob/9e803e9885d23064a24b138b0068a249f97d13ed/Eden/Nontransitivity.lean#L107-L110

import Definitions.Def_Eden_PeriodicOrbits
import Definitions.Def_Eden_StrictInvariance
import Definitions.Def_Eden_Nontransitivity
set_option autoImplicit true
noncomputable section
open Set
open Eden

theorem Eden.evolution_inner_disjoint_outer (c : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    Disjoint (evolution c t '' innerRadialRegion) outerRadialRegion := by sorry
