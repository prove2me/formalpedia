-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_cutSet_compact
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.cutSet_compact
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:04:46.776881+00:00
-- url     : https://prove2.me/theorems/e7fd9e63-73e2-4d9c-b894-16acd1ce1aeb
-- title:
--   Germ Sum Lattices: cut Set compact
-- statement:
--   The Germ Sum Lattices construction uses the cut Set compact property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L69-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L69-L84

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

theorem Formalism.FourierDecayAlt.P.GermSumLattices.cutSet_compact (m : ℕ) {Om : Set K} (hOm : IsCompact Om) (t : Kˣ) :
    IsCompact (cutSet m Om t) := by sorry
