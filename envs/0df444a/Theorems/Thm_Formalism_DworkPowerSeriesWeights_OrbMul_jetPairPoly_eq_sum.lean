-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OrbMul_jetPairPoly_eq_sum
-- name    : Formalism.DworkPowerSeriesWeights.OrbMul.jetPairPoly_eq_sum
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:56:46.873798+00:00
-- url     : https://prove2.me/theorems/60bcaa6e-7840-4b39-a8e9-7caf1cc2ff08
-- title:
--   Orb Mul: jet Pair Poly eq sum
-- statement:
--   The Orb Mul construction uses the jet Pair Poly eq sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L19-L25
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L19-L25

import Definitions.Def_Formalism_GaussJetBounds_GenLogInverse
import Definitions.Def_Formalism_GaussJetBounds_StatementW
import Definitions.Def_Formalism_GaussJetBounds_ThmAGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OneGauss
import Definitions.Def_Formalism_GaussJetBounds_GaussJetProofs_OrbMul
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
open Formalism Formalism.DworkPowerSeriesWeights
open Formalism.IncomingBounds
open Formalism.DworkPowerSeriesWeights.OrbMul
variable {K : Type} [Field K] {σ ι : Type}

theorem Formalism.DworkPowerSeriesWeights.OrbMul.jetPairPoly_eq_sum (P : MvPolynomial ι (MvPolynomial σ K)) (Th : MvPowerSeries ι K)
    (S : Finset (ι →₀ ℕ)) (hS : P.support ⊆ S) :
    jetPairPoly P Th = ∑ κ ∈ S, MvPolynomial.coeff κ P *
      MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th) := by sorry
