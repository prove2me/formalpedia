-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_symm_diag
-- name    : Formalism.L2.Th1.H.symm_diag
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:11:52.83029+00:00
-- url     : https://prove2.me/theorems/3a7b8283-bf97-4421-acb2-92330c21694a
-- title:
--   H: symm diag
-- statement:
--   The H construction uses the symm diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyIdentity.lean#L27-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyIdentity.lean#L27-L44

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_KerPNonzero
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_QuadraticSemicharacters_CayleyGaussianIntegrals_CayleyIdentity
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators ComplexConjugate
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.H
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem Formalism.L2.Th1.H.symm_diag [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (T : V →ₗ[ℂ] V)
    (hT : ∀ x y, H (T x) y = H x (T y)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (t : Fin (Module.finrank ℂ V) → ℝ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ ∀ i, T (b i) = (t i : ℂ) • b i := by sorry
