-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_cut_finite
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.cut_finite
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:34.995561+00:00
-- url     : https://prove2.me/theorems/294d54d2-1a41-49fc-9ad1-720e8d3a54c0
-- title:
--   Germ Sum Lattices: cut finite
-- statement:
--   The Germ Sum Lattices construction uses the cut finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L60-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L60-L67

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GermSumLattices
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Filter Topology
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.GermSumLattices
variable {K : Type} [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]

theorem Formalism.FourierDecayAlt.P.GermSumLattices.cut_finite (R : Subring K) (hRo : IsOpen (R : Set K)) {S : Set K} (hS : IsCompact S)
    (cr : K ⧸ R.toAddSubgroup → Kˣ) (hcr : IsCr R cr) : {x | (cr x : K) ∈ S}.Finite := by sorry
