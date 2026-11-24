-- Prove2me | Theorems.Thm_Formalism_L2_Th1_H_cayley_diag
-- name    : Formalism.L2.Th1.H.cayley_diag
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T09:48:45.15367+00:00
-- url     : https://prove2.me/theorems/56e1fef4-c296-4d2e-b446-fbcec31d5aef
-- title:
--   H: cayley diag
-- statement:
--   The H construction uses the cayley diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyIdentity.lean#L46-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/TorsionIntegrality/QuadraticSemicharacters/CayleyGaussianIntegrals/CayleyIdentity.lean#L46-L90

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

theorem Formalism.L2.Th1.H.cayley_diag [FiniteDimensional ℂ V] (H : Sesq V) (hH : IsHerm H) (hP : IsPosDef H) (Ae : V ≃ₗ[ℂ] V)
    (hA : ∀ u v, H (Ae u) v + H u (Ae v) = H (Ae u) (Ae v)) :
    ∃ (b : Module.Basis (Fin (Module.finrank ℂ V)) ℂ V) (l : Fin (Module.finrank ℂ V) → ℂ),
      (∀ i j, H (b i) (b j) = if i = j then 1 else 0) ∧ (∀ i, Ae (b i) = l i • b i) ∧ ∀ i, 0 < (l i).re := by sorry
