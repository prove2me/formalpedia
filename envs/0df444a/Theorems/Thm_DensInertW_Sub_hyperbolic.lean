-- Prove2me | Theorems.Thm_DensInertW_Sub_hyperbolic
-- name    : DensInertW.Sub.hyperbolic
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T11:17:46.198054+00:00
-- url     : https://prove2.me/theorems/0b949d89-0f08-5bae-a25e-1f3d79162694
-- title:
--   Sub: hyperbolic
-- statement:
--   The Sub construction uses the hyperbolic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L150-L217
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/PeriodIntegrals/UnitaryGroupMassFormula/InertDensity/FinrankInfKerAddOne.lean#L150-L217

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_AnisoPeelAlt
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_InertDensity_FinrankInfKerAddOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Module
open DensInertW DensInertW.Sub
variable {L : Type} [Field L]
variable {n : ℕ} {q : ℕ} {M : Matrix (Fin n) (Fin n) L}

theorem DensInertW.Sub.hyperbolic (hadd : ∀ a b : L, (a + b) ^ q = a ^ q + b ^ q)
    (hinv : ∀ a : L, (a ^ q) ^ q = a) (hM : ∀ k l, M l k = M k l ^ q)
    (htrs : ∀ s : L, s ^ q = s → ∃ t : L, t + t ^ q = s)
    (W : Submodule L (Fin n → L)) (hW : NonDeg q M W) (x : Fin n → L) (hx : x ∈ W)
    (hx0 : x ≠ 0) (hxx : hf q M x x = 0) :
    ∃ y ∈ W, hf q M x y = 1 ∧ hf q M y y = 0 ∧
      finrank L ↥(W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y)) + 2 =
        finrank L ↥W ∧
      NonDeg q M (W ⊓ LinearMap.ker (hfL q M x) ⊓ LinearMap.ker (hfL q M y)) := by sorry
