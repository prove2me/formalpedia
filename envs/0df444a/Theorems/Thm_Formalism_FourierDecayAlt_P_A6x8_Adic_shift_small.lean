-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x8_Adic_shift_small
-- name    : Formalism.FourierDecayAlt.P.A6x8.Adic.shift_small
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T19:44:42.413195+00:00
-- url     : https://prove2.me/theorems/33507be9-19ab-4b84-9cd8-0ce70d8c07d1
-- title:
--   Adic: shift small
-- statement:
--   The Adic construction uses the shift small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L260-L266
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GramKernelHermitian.lean#L260-L266

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

theorem Formalism.FourierDecayAlt.P.A6x8.Adic.shift_small (h : Adic R ϖ) (Sg : Finset K) (a : Kˣ) :
    ∃ V ∈ 𝓝 (0 : K), ∀ t ∈ V, ∀ σ ∈ Sg, σ * t ∈ I R (a : K) := by sorry
