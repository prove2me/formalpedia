-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_InverseBoundedFixedPoint_Adic_fp
-- name    : Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.fp
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T01:47:04.640665+00:00
-- url     : https://prove2.me/theorems/cddad1ac-d7d9-4a34-b36e-3031e1fa8502
-- title:
--   Adic: fp
-- statement:
--   The Adic construction uses the fp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L288-L318
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/SubmoduleMultiplication.lean#L288-L318

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SubmoduleMultiplication
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.A5 Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
variable {R : Subring K} {ϖ : Kˣ}

theorem Formalism.FourierDecayAlt.P.InverseBoundedFixedPoint.Adic.fp (h : Adic R ϖ) {E ι : Type} [TopologicalSpace E] (co : ι → E → K)
    (hco : ∀ i, Continuous (co i)) (hinj : ∀ x y, (∀ i, co i x = co i y) → x = y)
    (X : Set E) (hX : IsCompact X) (hXc : IsClosed X) (hne : X.Nonempty)
    (hXR : ∀ x ∈ X, ∀ i, co i x ∈ R) (T : E → E) (hT : ∀ x ∈ X, T x ∈ X)
    (hc : ∀ n, ∀ x ∈ X, ∀ y ∈ X, (∀ i, co i x - co i y ∈ I R ((ϖ : K) ^ n)) →
      ∀ i, co i (T x) - co i (T y) ∈ I R ((ϖ : K) ^ (n + 1))) : ∃ x ∈ X, T x = x := by sorry
