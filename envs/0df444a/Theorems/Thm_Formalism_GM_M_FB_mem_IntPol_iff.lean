-- Prove2me | Theorems.Thm_Formalism_GM_M_FB_mem_IntPol_iff
-- name    : Formalism.GM.M.FB.mem_IntPol_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:16:08.944965+00:00
-- url     : https://prove2.me/theorems/a993f7ef-68df-4616-a2a3-4e17b681644a
-- title:
--   FB: mem Int Pol iff
-- statement:
--   The FB construction uses the mem Int Pol iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L392-L395
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeBij.lean#L392-L395

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeBij
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
set_option linter.unusedSimpArgs false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.FB
open MvPolynomial Finset
variable {p : ℕ} [Fact p.Prime] {N r : ℕ}

theorem Formalism.GM.M.FB.mem_IntPol_iff {σ : Type} (x : MvPolynomial σ ℚ_[p]) :
    x ∈ IntPol p σ ↔ (x.coeffs : Set ℚ_[p]) ⊆ Set.range (algebraMap ℤ_[p] ℚ_[p]) := by sorry
