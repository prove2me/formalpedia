-- Prove2me | Theorems.Thm_Formalism_MainNotions_flipOneThree_Pf_KP_lemmaSMat
-- name    : Formalism.MainNotions.flipOneThree.Pf.KP.lemmaSMat
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-22T23:37:26.20387+00:00
-- url     : https://prove2.me/theorems/40782be4-4162-496f-84dd-2cad6021d51d
-- title:
--   KP: lemma SMat
-- statement:
--   The KP construction uses the lemma SMat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/LemmaSMat.lean#L54-L168
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/SharpRestriction/GrowthBounds/ColumnSpanDensity/LemmaSMat.lean#L54-L168

import Mathlib
import Definitions.Def_Formalism_SharpRestriction_GrowthBounds_ColumnSpanDensity_LemmaSMat
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.MainNotions Formalism.MainNotions.flipOneThree Formalism.MainNotions.flipOneThree.Pf Formalism.MainNotions.flipOneThree.Pf.KP
open Module
variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

theorem Formalism.MainNotions.flipOneThree.Pf.KP.lemmaSMat {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (σ ρ : ℕ) (z1 z2 : O) (h1 : z1 ≠ 0) (h2 : z2 ≠ 0) (N : Matrix (Fin σ) (Fin ρ) O) (B : Matrix (Fin ρ) (Fin σ) O) :
  ∃ (r s : ℕ), r + s = σ ∧
    (∃ (P : Matrix (Fin r) (Fin σ) O) (Q : Matrix (Fin ρ) (Fin r) O), P * N * Q = (z1 * z2) • (1 : Matrix (Fin r) (Fin r) O)) ∧
    (∃ (P' : Matrix (Fin s) (Fin σ) O) (P'' : Matrix (Fin σ) (Fin s) O) (M : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O), P' * P'' = 1 ∧
      Matrix.fromBlocks (z1 • (1 : Matrix (Fin s) (Fin s) O)) (P' * N) (B * P'') (z2 • (1 : Matrix (Fin ρ) (Fin ρ) O)) * M = (z1 * z2) • (1 : Matrix (Fin s ⊕ Fin ρ) (Fin s ⊕ Fin ρ) O)) := by sorry
