-- Prove2me | Theorems.Thm_Formalism_FrobeniusOrbits_ThickExists_sphere_rel
-- name    : Formalism.FrobeniusOrbits.ThickExists.sphere_rel
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:05:35.66581+00:00
-- url     : https://prove2.me/theorems/41e29f68-b5b0-4e3f-be8f-446ea72ab7e7
-- title:
--   Thick Exists: sphere rel
-- statement:
--   The Thick Exists construction uses the sphere rel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L36-L72
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/FrobeniusOrbits/FrobeniusOrbitsProofs/ThickExists.lean#L36-L72

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_HostThickExists
import Definitions.Def_Lemmata_GeneralBFactSecondLast_Imports
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_ThickExists
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.ThickExists

theorem Formalism.FrobeniusOrbits.ThickExists.sphere_rel {S : ℕ} (v₁ v₂ v₃ : Fin S → ℤ) (k : ℤ) (h₁ : ∑ m, v₁ m ^ 2 = k)
    (h₂ : ∑ m, v₂ m ^ 2 = k) (h₃ : ∑ m, v₃ m ^ 2 = k) (i j : ℤ) (hj : j ≠ 0) (hij : i ≠ j)
    (h : ∀ m, j * (v₂ m - v₁ m) = i * (v₃ m - v₁ m)) : v₂ = v₁ := by sorry
