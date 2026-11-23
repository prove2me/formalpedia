-- Prove2me | Theorems.Thm_Formalism_DoubleCosetMeasures_P_LemmaU_II_mul
-- name    : Formalism.DoubleCosetMeasures.P.LemmaU.II_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:50:46.692605+00:00
-- url     : https://prove2.me/theorems/a10edd57-6c5b-46ac-a59c-56cbd1f2c243
-- title:
--   Lemma U: II mul
-- statement:
--   The Lemma U construction uses the II mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LemmaU.lean#L38-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/DoubleCosetMeasures/LowerUnipotentOrbits/LemmaU.lean#L38-L46

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

theorem Formalism.DoubleCosetMeasures.P.LemmaU.II_mul (O : Subring F) (ϖ : F) (y : Matrix (Fin t) (Fin a) F) (hy : y ∈ IIset O ϖ)
    (g : Matrix (Fin a) (Fin a) F) (hg : ∀ i j, g i j ∈ O) : y * g ∈ IIset O ϖ := by sorry
