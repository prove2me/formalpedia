-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OrbMul_jetPairPoly_monomial
-- name    : Formalism.DworkPowerSeriesWeights.OrbMul.jetPairPoly_monomial
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:58:27.824165+00:00
-- url     : https://prove2.me/theorems/b9798881-8241-440b-a911-4dcee177a623
-- title:
--   Orb Mul: jet Pair Poly monomial
-- statement:
--   The Orb Mul construction uses the jet Pair Poly monomial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L37-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L37-L42

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

theorem Formalism.DworkPowerSeriesWeights.OrbMul.jetPairPoly_monomial (κ : ι →₀ ℕ) (c : MvPolynomial σ K) (Th : MvPowerSeries ι K) :
    jetPairPoly (MvPolynomial.monomial κ c) Th =
      c * MvPolynomial.C (((mfact κ : ℕ) : K) * MvPowerSeries.coeff κ Th) := by sorry
