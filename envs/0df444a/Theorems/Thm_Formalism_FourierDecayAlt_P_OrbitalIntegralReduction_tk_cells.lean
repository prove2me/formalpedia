-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_cells
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_cells
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:29:28.638054+00:00
-- url     : https://prove2.me/theorems/1b3dfd52-94ff-4d27-8a27-4edfc823fcb4
-- title:
--   Orbital Integral Reduction: tk cells
-- statement:
--   The Orbital Integral Reduction construction uses the tk cells property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L580-L631
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L580-L631

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
variable {V : Type} [AddCommGroup V]
variable [TopologicalSpace V] [IsTopologicalAddGroup V]

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_cells {V₀ : AddSubgroup V} (h0 : Lat V₀) {Q : Type} (c : Q → V) (N : Q → AddSubgroup V)
    (hN : ∀ q, Lat (N q)) (hpart : ∀ v, ∃! q, v - c q ∈ N q) (f : V → ℂ)
    (hf : ∀ q, ∀ w ∈ N q, f (c q + w) = f (c q)) (hfin : {q | f (c q) ≠ 0}.Finite)
    {M : AddSubgroup V} (hM : Lat M) (hinv : ∀ v, ∀ l ∈ M, f (v + l) = f v) :
    tk_S V₀ M f = ∑ᶠ q, (gi (N q) V₀ : ℂ) * f (c q) := by sorry
