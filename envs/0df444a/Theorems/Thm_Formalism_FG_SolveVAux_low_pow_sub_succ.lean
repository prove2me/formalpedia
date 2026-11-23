-- Prove2me | Theorems.Thm_Formalism_FG_SolveVAux_low_pow_sub_succ
-- name    : Formalism.FG.SolveVAux.low_pow_sub_succ
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:24:01.17557+00:00
-- url     : https://prove2.me/theorems/84376fac-2967-4b04-b8bc-fdf51fa64476
-- title:
--   Solve VAux: low pow sub succ
-- statement:
--   The Solve VAux construction uses the low pow sub succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L111-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FormalGroupWitt/FormalGroupWittProofs/SolveV.lean#L111-L133

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
variable {R : Type u} [CommRing R] {ι : Type v} {τ : Type w}

theorem Formalism.FG.SolveVAux.low_pow_sub_succ {M : ℕ} {k k' : ι → MvPowerSeries τ R} (hk : ∀ i, Low 1 (k i))
    (hk' : ∀ i, Low 1 (k' i)) (hkk : ∀ i, Low M (k i - k' i)) (e : ι →₀ ℕ)
    (he : 2 ≤ e.degree) : Low (M + 1) (P k e - P k' e) := by sorry
