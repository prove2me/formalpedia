-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_succ_dvd_total
-- name    : Formalism.DworkPowerSeriesWeights.succ_dvd_total
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:56.411798+00:00
-- url     : https://prove2.me/theorems/108cbdf4-97ce-48d3-a975-2f0112431b08
-- title:
--   Dwork Power Series Weights: succ dvd total
-- statement:
--   The Dwork Power Series Weights construction uses the succ dvd total property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneLetterRadiusIdentity.lean#L26-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OneLetterRadiusIdentity.lean#L26-L42

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneLetterRadiusIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
universe u
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.succ_dvd_total {l d : ℕ} (hl : 1 ≤ l) (hd : Even d) {ι : Type*} (n : ι →₀ ℕ)
    (f : ι → ZMod d)
    (h : ((l ^ d - 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) * lw l (f x)) :
    ((l + 1 : ℕ) : ℤ) ∣ ∑ x ∈ n.support, (n x : ℤ) := by sorry
