-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_inv_bounded
-- name    : Formalism.FourierDecayAlt.P.A6x8.Adic.inv_bounded
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:28:58.443018+00:00
-- url     : https://prove2.me/theorems/023cb741-679f-4661-ab56-b18238c99499
-- title:
--   Adic: inv bounded
-- statement:
--   The Adic construction uses the inv bounded property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L295-L324
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L295-L324

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x8
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.A6x8.Adic.inv_bounded (h : Adic R ϖ) {Om : Set K} (hC : IsCompact Om) (hU : ∀ z ∈ Om, IsUnit z) :
    ∃ M : ℕ, ∀ z ∈ Om, ∀ z' : K, z * z' = 1 → (ϖ : K) ^ M * z' ∈ R := by sorry
