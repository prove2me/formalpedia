-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_subst_sub
-- name    : Formalism.FG.SolveVAux.low_subst_sub
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:41:14.953528+00:00
-- url     : https://prove2.me/theorems/d1c1ce06-e59a-43d4-a93e-36639bd59d04
-- title:
--   Solve VAux: low subst sub
-- statement:
--   The Solve VAux construction uses the low subst sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L149-L164
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L149-L164

import Definitions.Def_Formalism_FormalGroupWitt_SubstInjectiveV
import Definitions.Def_Formalism_FormalGroupWitt_FormalGroupWittProofs_SolveV
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
universe u v w
open Formalism Formalism.FG Formalism.FG.SolveVAux
open MvPowerSeries
variable {R : Type u} [CommRing R] {ι : Type v} [Finite ι] {τ : Type w}

theorem Formalism.FG.SolveVAux.low_subst_sub {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i))
    (hk' : ∀ i, Low 1 (k' i)) (hkk : ∀ i, Low M (k i - k' i)) {g : MvPowerSeries ι R}
    (hg : Low 2 g) : Low (M + 1) (subst k g - subst k' g) := by sorry
