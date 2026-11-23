-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A6x3_finsum_fst
-- name    : Formalism.FourierDecayAlt.P.A6x3.finsum_fst
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:02:44.588286+00:00
-- url     : https://prove2.me/theorems/a0239505-8b7c-4a90-9572-cf4585599b9b
-- title:
--   A6x3: finsum fst
-- statement:
--   The A6x3 construction uses the finsum fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L10-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/IntegralLatticeRefinementIdentity.lean#L10-L32

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A6x3

theorem Formalism.FourierDecayAlt.P.A6x3.finsum_fst {X Y Z : Type} [Finite Z] [Nonempty Z] (e : X ≃ Y × Z) (G : Y → ℂ) :
    ∑ᶠ x, G (e x).1 = (Nat.card Z : ℂ) * ∑ᶠ y, G y := by sorry
