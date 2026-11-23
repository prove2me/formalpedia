-- Prove2me | Theorems.Thm_Formalism_FourierDecayAlt_P_A5x9_lift_abs
-- name    : Formalism.FourierDecayAlt.P.A5x9.lift_abs
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:46:08.716629+00:00
-- url     : https://prove2.me/theorems/b9c01bd2-b934-4c91-abd0-1fcb0f0d7187
-- title:
--   A5x9: lift abs
-- statement:
--   The A5x9 construction uses the lift abs property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L88-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/HermitianCurvature/HermitianCurvatureProofs/LatticeAverageIdentity.lean#L88-L150

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ColumnOperationTripleForm
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_KernelQuotientFinite
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_LatticeAverageIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x9

theorem Formalism.FourierDecayAlt.P.A5x9.lift_abs {R P P' V : Type} [CommRing R] [AddCommGroup P] [Module R P] [AddCommGroup P']
    [Module R P'] [AddCommGroup V] [Module R V]
    (L S0 : Submodule R P) (L' S0' : Submodule R P') (Λ : P →ₗ[R] V) (Λ' : P' →ₗ[R] V)
    (DD : V →ₗ[R] V) (φ : (P ⧸ L) ≃ₗ[R] (P' ⧸ L'))
    (hS : S0 ≤ L) (hS' : S0' ≤ L') (hk : ∀ x ∈ S0, Λ x = 0) (hk' : ∀ y ∈ S0', Λ' y = 0)
    (h1 : ∀ x ∈ L, DD (Λ x) = 0 → x ∈ S0) (h1' : ∀ y ∈ L', Λ' y = 0 → y ∈ S0')
    (h2 : ∀ x, ∃ y, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧ Λ' y = DD (Λ x))
    (h3 : ∀ y, ∃ x, φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧ Λ' y = DD (Λ x)) :
    ∃ Ψ : (P ⧸ S0) ≃ₗ[R] (P' ⧸ S0'), ∀ x y, Ψ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ↔
      (φ (Submodule.Quotient.mk x) = Submodule.Quotient.mk y ∧ Λ' y = DD (Λ x)) := by sorry
