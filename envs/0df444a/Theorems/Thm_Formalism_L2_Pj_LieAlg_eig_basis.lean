-- Prove2me | Theorems.Thm_Formalism_L2_Pj_LieAlg_eig_basis
-- name    : Formalism.L2.Pj.LieAlg.eig_basis
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T08:37:56.817208+00:00
-- url     : https://prove2.me/theorems/4d645684-474e-4ddf-994f-2d77253e6113
-- title:
--   Lie Alg: eig basis
-- statement:
--   The Lie Alg construction uses the eig basis property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieAlg.lean#L168-L259
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/ProjectiveLattices/LieAlg.lean#L168-L259

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_LieAlg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.LieAlg
open Submodule
variable {V K : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [Field K] [Algebra V K]
  [IsFractionRing V K]

theorem Formalism.L2.Pj.LieAlg.eig_basis {n m : ℕ} {ι : Type} (L : ι → (Fin n → V) →ₗ[V] (Fin n → V)) (χ : ι → V)
    (M : ι → (Fin n → K) →ₗ[K] (Fin n → K))
    (hM : ∀ a c, M a (fun j => algebraMap V K (c j)) = fun j => algebraMap V K (L a c j))
    (v : Fin m → (Fin n → K)) (hv : ∀ a i, M a (v i) = algebraMap V K (χ a) • v i)
    (hb : ∀ w, (∀ a, M a w = algebraMap V K (χ a) • w) → ∃! cf : Fin m → K, w = ∑ i, cf i • v i) :
    ∃ b : Fin m → (Fin n → V), (∀ a i, L a (b i) = χ a • b i) ∧
      (∀ c, (∀ a, L a c = χ a • c) → ∃! r : Fin m → V, c = ∑ i, r i • b i) ∧
      ∀ i, ∃ cf : Fin m → K, cf i ≠ 0 ∧ (∀ j, i < j → cf j = 0) ∧
        (fun j => algebraMap V K (b i j)) = ∑ j, cf j • v j := by sorry
