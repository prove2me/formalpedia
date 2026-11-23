-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_OrbitalIntegralReduction_tk_reindex
-- name    : Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_reindex
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:17:34.263845+00:00
-- url     : https://prove2.me/theorems/cec0feb5-cb49-4ea0-8528-6326c3c9057b
-- title:
--   Orbital Integral Reduction: tk reindex
-- statement:
--   The Orbital Integral Reduction construction uses the tk reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L257-L270
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/OrbitalIntegralReduction.lean#L257-L270

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

theorem Formalism.FourierDecayAlt.P.OrbitalIntegralReduction.tk_reindex {X Q₁ Q₂ : Type} (π₁ : X → Q₁) (π₂ : X → Q₂) (s₁ : Q₁ → X) (s₂ : Q₂ → X)
    (h₁ : ∀ q, π₁ (s₁ q) = q) (h₂ : ∀ q, π₂ (s₂ q) = q)
    (hk : ∀ x x', π₁ x = π₁ x' ↔ π₂ x = π₂ x') (f : X → ℂ)
    (hf : ∀ x x', π₁ x = π₁ x' → f x = f x') : ∑ᶠ q, f (s₁ q) = ∑ᶠ q, f (s₂ q) := by sorry
