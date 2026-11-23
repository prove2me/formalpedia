-- Prove2me | Theorems.Thm_Formalism_DworkPowerSeriesWeights_OrbMul_jetPairPoly_add_left
-- name    : Formalism.DworkPowerSeriesWeights.OrbMul.jetPairPoly_add_left
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T06:57:50.013797+00:00
-- url     : https://prove2.me/theorems/90c3a826-2178-40fa-8453-a321cc2df85f
-- title:
--   Orb Mul: jet Pair Poly add left
-- statement:
--   The Orb Mul construction uses the jet Pair Poly add left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L27-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaussJetBounds/GaussJetProofs/OrbMul.lean#L27-L35

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

theorem Formalism.DworkPowerSeriesWeights.OrbMul.jetPairPoly_add_left (P Q : MvPolynomial ι (MvPolynomial σ K)) (Th : MvPowerSeries ι K) :
    jetPairPoly (P + Q) Th = jetPairPoly P Th + jetPairPoly Q Th := by sorry
