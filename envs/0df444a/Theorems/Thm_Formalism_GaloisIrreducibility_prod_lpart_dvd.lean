-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_prod_lpart_dvd
-- name    : Formalism.GaloisIrreducibility.prod_lpart_dvd
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:53:24.318163+00:00
-- url     : https://prove2.me/theorems/c3ce2a62-0928-4cf5-bce5-99fa3e509b1e
-- title:
--   Galois Irreducibility: prod lpart dvd
-- statement:
--   The Galois Irreducibility construction uses the prod lpart dvd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/FewLargeParts.lean#L7-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/FewLargeParts.lean#L7-L22

import Definitions.Def_Formalism_GaloisIrreducibility_Statement
import Definitions.Def_Formalism_GaloisIrreducibility_GaloisIrreducibilityProofs_FewLargeParts
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

theorem Formalism.GaloisIrreducibility.prod_lpart_dvd (n : ℕ) (S : Finset ℕ) (hS : ∀ l ∈ S, l.Prime) :
    (∏ l ∈ S, l ^ padicValNat l n) ∣ n := by sorry
