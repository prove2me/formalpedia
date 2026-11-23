-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_cut_mem
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.cut_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:05:25.715976+00:00
-- url     : https://prove2.me/theorems/c2b74450-90cc-4064-b68c-0b021eaade2c
-- title:
--   Germ Sum Lattices: cut mem
-- statement:
--   The Germ Sum Lattices construction uses the cut mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L470-L480
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L470-L480

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
variable {K : Type} [CommRing K]

theorem Formalism.FourierDecayAlt.P.GermSumLattices.cut_mem [TopologicalSpace K] (m : ℕ) (Om : Set K) (hOm : IsOmega (m + 1) Om) (t c z : Kˣ)
    (hc : (c : K) ∈ cutSet m Om t) (hz : z ^ (m + 1) = (-t) ^ m * c) : (z : K) ∈ Om := by sorry
