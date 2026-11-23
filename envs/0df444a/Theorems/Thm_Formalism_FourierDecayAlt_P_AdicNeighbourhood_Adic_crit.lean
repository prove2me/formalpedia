-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_AdicNeighbourhood_Adic_crit
-- name    : Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.crit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:55:13.088077+00:00
-- url     : https://prove2.me/theorems/687759ab-ed99-4594-ae23-213b7e2ba75f
-- title:
--   Adic: crit
-- statement:
--   The Adic construction uses the crit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L236-L295
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/AdicNeighbourhood.lean#L236-L295

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

theorem Formalism.FourierDecayAlt.P.AdicNeighbourhood.Adic.crit (h : Adic R ϖ) (hn : ∀ n : ℕ, n ≠ 0 → IsUnit (n : K)) (m a : ℕ)
    (B : AddSubgroup K) (hB : (B : Set K) ∈ 𝓝 (0 : K)) :
    ∃ j : ℕ, ∀ (D : Kˣ) (x xi : Fin m → K), (∀ k, x k * xi k = 1) →
      (∀ k, (ϖ : K) ^ a * x k ∈ R) →
      (∀ k, 1 - (D : K) * (xi k * ∏ i, xi i) ∈ I R ((ϖ : K) ^ j)) →
      ∃ z : Kˣ, z ^ (m + 1) = D ∧ ∀ k, x k - (z : K) ∈ B := by sorry
