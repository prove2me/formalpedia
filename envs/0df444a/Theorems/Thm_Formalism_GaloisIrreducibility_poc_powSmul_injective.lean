-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_poc_powSmul_injective
-- name    : Formalism.GaloisIrreducibility.poc_powSmul_injective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:26.554798+00:00
-- url     : https://prove2.me/theorems/63439bbf-caab-4c3d-8011-67967ebf59ff
-- title:
--   Galois Irreducibility: poc pow Smul injective
-- statement:
--   The Galois Irreducibility construction uses the poc pow Smul injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PrimitiveOfPCycle.lean#L7-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/PrimitiveOfPCycle.lean#L7-L35

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_PrimitiveOfPCycle
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open scoped Pointwise

theorem Formalism.GaloisIrreducibility.poc_powSmul_injective {M Y : Type*} [Group M] [MulAction M Y] (s : M) (p : ℕ) (hp : p.Prime)
    (hs : s ^ p = 1) (y : Y) (hy : s • y ≠ y) :
    ∀ i < p, ∀ j < p, s ^ i • y = s ^ j • y → i = j := by sorry
