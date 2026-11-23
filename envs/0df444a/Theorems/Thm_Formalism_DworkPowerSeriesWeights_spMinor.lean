-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_spMinor
-- name    : Formalism.DworkPowerSeriesWeights.spMinor
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T18:07:43.191998+00:00
-- url     : https://prove2.me/theorems/089ccdf7-5c6e-4fcc-8763-f891e14e5ce6
-- title:
--   Dwork Power Series Weights: sp Minor
-- statement:
--   The Dwork Power Series Weights construction uses the sp Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L351-L406
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/Special.lean#L351-L406

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementB
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_Special
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
universe u v
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
variable {R : Type*} [CommRing R] {m p : ℕ}

theorem Formalism.DworkPowerSeriesWeights.spMinor (top : Fin (p + 1) → R) (A : Matrix (Fin (p + 1)) (Fin (p + 1))
      (MvPolynomial (Fin m × Fin (p + 1)) R)) (cf : Fin (p + 1) → Option (Fin m) → R)
    (hA : ∀ i c, A i c = ∑ o, MvPolynomial.C (cf i o) * spV top o c) :
    ∀ mono ∈ A.det.support, ∀ k : Fin m, (∑ c : Fin (p + 1), mono (k, c)) ≤ 1 := by sorry
