-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_GermSumLattices_finsum_if
-- name    : Formalism.FourierDecayAlt.P.GermSumLattices.finsum_if
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T21:56:05.912014+00:00
-- url     : https://prove2.me/theorems/a2b3eeab-f9de-4c9f-8e9c-694cc43b3878
-- title:
--   Germ Sum Lattices: finsum if
-- statement:
--   The Germ Sum Lattices construction uses the finsum if property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L10-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/GermSumLattices.lean#L10-L21

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

theorem Formalism.FourierDecayAlt.P.GermSumLattices.finsum_if {α : Type} {P : α → Prop} {inst : DecidablePred P} (hfin : {x | P x}.Finite)
    (G : α → ℂ) : ∑ᶠ x, (if P x then G x else 0) = ∑ x ∈ hfin.toFinset, G x := by sorry
