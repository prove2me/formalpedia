-- Prove2me | Theorems.Thm_Formalism_GM_FrozenVariableComponents_hom_aeval
-- name    : Formalism.GM.FrozenVariableComponents.hom_aeval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:20.155973+00:00
-- url     : https://prove2.me/theorems/b6346335-baed-474b-9084-0ccb4bd167f6
-- title:
--   Frozen Variable Components: hom aeval
-- statement:
--   The Frozen Variable Components construction uses the hom aeval property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L904-L919
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/MahlerMeasure/MahlerMeasureProofs/FreezeY.lean#L904-L919

import Definitions.Def_Formalism_MahlerMeasure_IsFrozenInv
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_FreezeY
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.FrozenVariableComponents
open MvPolynomial Finset Formalism.GM.M
variable {K : Type*} [CommRing K]

theorem Formalism.GM.FrozenVariableComponents.hom_aeval {σ τ : Type*} (w : τ → ℕ) (v : σ → ℕ) (g : σ → MvPolynomial τ K)
    (hg : ∀ x, IsWeightedHomogeneous w (g x) (v x)) (f : MvPolynomial σ K) (d : ℕ)
    (hf : IsWeightedHomogeneous v f d) : IsWeightedHomogeneous w (aeval g f) d := by sorry
