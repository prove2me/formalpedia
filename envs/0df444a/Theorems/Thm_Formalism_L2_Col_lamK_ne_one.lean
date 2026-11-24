-- Prove2me | Theorems.Thm_Formalism_L2_Col_lamK_ne_one
-- name    : Formalism.L2.Col.lamK_ne_one
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T07:49:44.541818+00:00
-- url     : https://prove2.me/theorems/b0c682ef-97a6-4628-ad9d-904abf2bf56a
-- title:
--   Col: lam K ne one
-- statement:
--   The Col construction uses the lam K ne one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L565-L580
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/LocalToGlobal/Columns/LevGCount.lean#L565-L580

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Columns_GenericUnipotentCharacter
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DimensionMassJointBound
import Definitions.Def_Formalism_LocalToGlobal_Columns_LevGCount
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Finset IsDedekindDomain NumberField
open Formalism Formalism.L2 Formalism.L2.Col
variable {n : ℕ} {κ : Type} [CommRing κ] {K : Type} [Field K]

theorem Formalism.L2.Col.lamK_ne_one (χ : ℕ → κˣ →* Kˣ) {r : ℕ} (bl : List ℕ) (i₀ : Fin n) {s : ℕ} (hs : s < bl.length)
    (h₀ : coarse r bl i₀.val = s + 1) (hχ : χ s ≠ 1) : lamK χ n r bl ≠ 1 := by sorry
