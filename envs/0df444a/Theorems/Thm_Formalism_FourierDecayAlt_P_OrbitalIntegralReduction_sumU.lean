-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_sumU
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.sumU
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:55.677434+00:00
-- url     : https://prove2.me/theorems/6dde4692-67e9-471d-b2cb-967d316a25f7
-- title:
--   Orbital Integral Reduction: sum U
-- statement:
--   The Orbital Integral Reduction construction uses the sum U property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L984-L1011
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L984-L1011

import Definitions.Def_Formalism_HermitianCurvature_ThetaExistenceInductiveFromPieces
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelNonzeroModulusDeterminantEq
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_FirstKernelExplicitFormula
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_IntegralLatticeRefinementIdentity
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GramKernelHermitian
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_OrbitalIntegralReduction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5 Formalism.FourierDecayAlt.A6 Formalism.FourierDecayAlt.P.A5x5 Formalism.FourierDecayAlt.P.A5x8 Formalism.FourierDecayAlt.P.A6x8 Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.OrbitalIntegralReduction
variable {K : Type} [CommRing K]
variable [TopologicalSpace K] [IsTopologicalRing K] {R : Subring K} {ψ : AddChar K ℂ}

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.sumU (hD : LocalDatum K R ψ) (n : ℕ) (f : Matrix (Fin n) (Fin n) K → ℂ)
    (hinv : ∀ u r : Matrix (Fin n) (Fin n) K, IsUpUni u → IsUpUni r → IsInt R r → f (u * r) = f u)
    (hfin : {q : upUniG K n ⧸ intSub R (upUniG K n) | f (sec_m (Quotient.out q)) ≠ 0}.Finite)
    {Λ : AddSubgroup K} (hΛ : IsLat Λ) (hΛinv : BInv Λ (fun y : Pr n → K => f (1 + EE y))) :
    ∑ᶠ q : upUniG K n ⧸ intSub R (upUniG K n), f (sec_m (Quotient.out q)) =
      bx R Λ (Pr n) (fun y => f (1 + EE y)) := by sorry
