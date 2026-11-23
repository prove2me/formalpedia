-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_taylor
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.taylor
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:25.152135+00:00
-- url     : https://prove2.me/theorems/3ab6f2b3-6c86-4dba-872f-c486cfa53293
-- title:
--   Adic: taylor
-- statement:
--   The Adic construction uses the taylor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L319-L360
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L319-L360

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AdicNeighbourhood
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Formalism.DoubleCosetMeasures Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.AdicNeighbourhood
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.taylor (h : Adic R ϖ) (m a : ℕ) (D : K) (x xi v : Fin m → K) (μ : K)
    (hμ : μ ∈ I R (ϖ : K)) (hx : ∀ k, x k * xi k = 1) (hxi : ∀ k, (ϖ : K) ^ a * xi k ∈ R)
    (hv : ∀ k, ∃ r ∈ R, v k = (ϖ : K) ^ a * μ * r) :
    ∃ ρ ∈ R, g0 D (x + v) = g0 D x + ∑ k, v k * (1 - D * (xi k * ∏ i, xi i)) +
      D * (∏ i, xi i) * μ ^ 2 * ρ := by sorry
