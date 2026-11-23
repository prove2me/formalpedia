-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_LemmaU_choose_eq
-- name    : Formalism.DoubleCosetMeasures.P.LemmaU.choose_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:51:10.487409+00:00
-- url     : https://prove2.me/theorems/29ec9d96-5c09-4c6d-ae34-fba0b69a69e3
-- title:
--   Lemma U: choose eq
-- statement:
--   The Lemma U construction uses the choose eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LemmaU.lean#L12-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LemmaU.lean#L12-L18

import Definitions.Def_Formalism_DoubleCosetMeasures_StatementZ
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LemmaU
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix ComplexConjugate
open Formalism Formalism.DoubleCosetMeasures Formalism.DoubleCosetMeasures.P Formalism.DoubleCosetMeasures.P.LemmaU
open Formalism.DoubleCosetMeasures
variable {F : Type} [Field F] {a t : ℕ}

theorem Formalism.DoubleCosetMeasures.P.LemmaU.choose_eq {J' : Subgroup (GL (Fin a) F)} {y : Matrix (Fin a) (Fin a) F}
    (h : ∃ k : J', ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = y) (k : J')
    (e : ((k : GL (Fin a) F) : Matrix (Fin a) (Fin a) F) = y) : Classical.choose h = k := by sorry
