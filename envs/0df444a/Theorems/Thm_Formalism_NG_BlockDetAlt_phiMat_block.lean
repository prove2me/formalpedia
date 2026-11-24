-- Prove2me | Theorems.Thm_Formalism_NG_BlockDetAlt_phiMat_block
-- name    : Formalism.NG.BlockDetAlt.phiMat_block
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T10:12:24.554414+00:00
-- url     : https://prove2.me/theorems/2a1da475-90de-4649-b66d-4f4c16e20dca
-- title:
--   Block Det Alt: phi Mat block
-- statement:
--   The Block Det Alt construction uses the phi Mat block property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L380-L393
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/CharacterColumnKernels/IdempotentNormalForms/IsUnitDetOfConst.lean#L380-L393

import Definitions.Def_Formalism_CharacterColumnKernels_StatementN
import Definitions.Def_Formalism_CharacterColumnKernels_IdempotentNormalForms_IsUnitDetOfConst
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
open Formalism Formalism.NG
open Formalism.NG.BlockDetAlt
variable {O : Type*} [CommRing O] {X' : Type*}
variable {d : Type} [Fintype d] [DecidableEq d]
variable {d : Type} [Fintype d] [DecidableEq d]

theorem Formalism.NG.BlockDetAlt.phiMat_block (R' : Subalgebra O (X' → Matrix d d (FractionRing O))) {g : Type} [Fintype g]
    [DecidableEq g] (Θ : Matrix g g R') (p q : g) (n : ℕ) :
    coefMat n (Matrix.of fun i j => phiMat R' Θ (p, i) (q, j)) =
      (if n = 0 ∧ p = q then 1 else 0) -
        (if n = 1 then (Θ p q : X' → Matrix d d (FractionRing O)) else 0) := by sorry
