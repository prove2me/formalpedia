-- Prove2me | Theorems.Thm_Formalism_GM_M_PhiIntegrality_bnd_sum
-- name    : Formalism.GM.M.PhiIntegrality.bnd_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T20:35:33.194174+00:00
-- url     : https://prove2.me/theorems/d0f9e878-bf8e-4fb6-a56c-f1118578c2b9
-- title:
--   Phi Integrality: bnd sum
-- statement:
--   The Phi Integrality construction uses the bnd sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L32-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/PhiInt.lean#L32-L42

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type}

theorem Formalism.GM.M.PhiIntegrality.bnd_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial σ ℚ_[p]) {B : ℝ} (hB : 0 ≤ B)
    (h : ∀ i ∈ s, Bnd B (f i)) : Bnd B (∑ i ∈ s, f i) := by sorry
