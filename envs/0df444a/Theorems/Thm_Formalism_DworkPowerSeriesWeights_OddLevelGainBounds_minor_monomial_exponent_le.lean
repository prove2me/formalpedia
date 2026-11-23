-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OddLevelGainBounds_minor_monomial_exponent_le
-- name    : Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.minor_monomial_exponent_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T17:53:12.248216+00:00
-- url     : https://prove2.me/theorems/54e2f496-849f-4a7c-9379-adf151d773ff
-- title:
--   Odd Level Gain Bounds: minor monomial exponent le
-- statement:
--   The Odd Level Gain Bounds construction uses the minor monomial exponent le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/OneLetterUnramifiedBound.lean#L57-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/OneLetterGaussJets/OneLetterGaussProofs/OneLetterUnramifiedBound.lean#L57-L77

import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_StatementG
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_WeightsAddOverOrbitFamily
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
import Definitions.Def_Formalism_GaussJetBounds_OneLetterGaussJets_OneLetterGaussProofs_OneLetterUnramifiedBound
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
open Formalism Formalism.DworkPowerSeriesWeights Formalism.DworkPowerSeriesWeights.OddLevelGainBounds
open Formalism.IncomingBounds

theorem Formalism.DworkPowerSeriesWeights.OddLevelGainBounds.minor_monomial_exponent_le {K : Type} [Field K] {N0 N1 C : ℕ} (p : Fin C → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) (κ : Fin N0 × Fin N1 →₀ ℕ)
    (hκ : κ ∈ (minorProd (fun (i : Fin N0) (b : Fin N1) =>
      (MvPolynomial.X (i, b) : MvPolynomial (Fin N0 × Fin N1) K)) p hp I).support)
    (y : Fin N0 × Fin N1) : κ y ≤ C := by sorry
