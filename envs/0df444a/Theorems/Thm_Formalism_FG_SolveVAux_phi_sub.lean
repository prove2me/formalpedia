-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_phi_sub
-- name    : Formalism.FG.SolveVAux.phi_sub
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:01.679984+00:00
-- url     : https://prove2.me/theorems/0588da53-59e7-491b-9127-e03ebc11befa
-- title:
--   Solve VAux: phi sub
-- statement:
--   The Solve VAux construction uses the phi sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L211-L219
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L211-L219

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
variable {G : ι → MvPowerSeries τ R} {g : ι → MvPowerSeries ι R}

theorem Formalism.FG.SolveVAux.phi_sub (hg : ∀ j, Low 2 (g j)) {M : ℕ} {k k' : ι → MvPowerSeries τ R}
    (hk : ∀ i, Low 1 (k i)) (hk' : ∀ i, Low 1 (k' i)) (hkk : ∀ i, Low M (k i - k' i)) (j : ι) :
    Low (M + 1) (phi G g k j - phi G g k' j) := by sorry
