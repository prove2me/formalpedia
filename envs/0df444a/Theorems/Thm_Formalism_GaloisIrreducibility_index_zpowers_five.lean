-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_index_zpowers_five
-- name    : Formalism.GaloisIrreducibility.index_zpowers_five
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:08.618474+00:00
-- url     : https://prove2.me/theorems/3d4ca0d6-1455-4d72-960d-993d1d62ac6c
-- title:
--   Galois Irreducibility: index zpowers five
-- statement:
--   The Galois Irreducibility construction uses the index zpowers five property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/ResiduesLe.lean#L68-L77
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/ResiduesLe.lean#L68-L77

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_ResiduesLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GaloisIrreducibility
open Finset

theorem Formalism.GaloisIrreducibility.index_zpowers_five (n : ℕ) (h : Nat.Coprime 5 (2 ^ (n + 2))) :
    (Subgroup.zpowers (ZMod.unitOfCoprime 5 h)).index = 2 := by sorry
