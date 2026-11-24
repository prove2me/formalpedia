-- Prove2me | Theorems.Thm_Formalism_MainNotions_FormalGroupSystem_Pf_descent_core
-- name    : Formalism.MainNotions.FormalGroupSystem.Pf.descent_core
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T09:17:06.955508+00:00
-- url     : https://prove2.me/theorems/edf2b6c2-c166-4ea5-948e-60cbfcdc7ea6
-- title:
--   Pf: descent core
-- statement:
--   The Pf construction uses the descent core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DescentCore.lean#L98-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/MultisetValuation/DescentCore.lean#L98-L172

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_MultisetValuation_DescentCore
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.FormalGroupSystem Formalism.MainNotions.FormalGroupSystem.Pf
open Finset

theorem Formalism.MainNotions.FormalGroupSystem.Pf.descent_core {K Kc V Vc M : Type*} [Field K] [Field Kc] [Algebra K Kc]
    [AddCommGroup V] [Module K V] [AddCommGroup Vc] [Module Kc Vc]
    (ι : V →+ Vc) (hιs : ∀ (c : K) (v : V), ι (c • v) = algebraMap K Kc c • ι v)
    (π : M → V →ₗ[K] K) (πc : M → Vc →ₗ[Kc] Kc) (hπ : ∀ m v, πc m (ι v) = algebraMap K Kc (π m v))
    (hsep : ∀ v : V, (∀ m, π m v = 0) → v = 0)
    (R : Subring K) (hR : ∀ x : K, x ∈ R ∨ x⁻¹ ∈ R)
    (A : AddSubgroup Kc) (hA : ∀ r ∈ R, ∀ a ∈ A, algebraMap K Kc r * a ∈ A) {κ : Type*} [DecidableEq κ] :
    ∀ (n : ℕ) (s : Finset κ), s.card = n → ∀ (z : κ → V) (a : κ → Kc), (∀ k ∈ s, a k ∈ A) → ∀ y : V,
      ι y = ∑ k ∈ s, a k • ι (z k) →
      ∃ c : κ → K, (∀ k ∈ s, algebraMap K Kc (c k) ∈ A) ∧ y = ∑ k ∈ s, c k • z k := by sorry
