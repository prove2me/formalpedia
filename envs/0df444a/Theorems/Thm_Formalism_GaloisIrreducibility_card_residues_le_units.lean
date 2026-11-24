-- Prove2me | Theorems.Thm_Formalism_GaloisIrreducibility_card_residues_le_units
-- name    : Formalism.GaloisIrreducibility.card_residues_le_units
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T22:52:59.524154+00:00
-- url     : https://prove2.me/theorems/907fea59-c62d-4604-80c6-dfd2655b2d46
-- title:
--   Galois Irreducibility: card residues le units
-- statement:
--   The Galois Irreducibility construction uses the card residues le units property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/ResiduesLe.lean#L37-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Formalism/GaloisIrreducibility/GaloisIrreducibilityProofs/ResiduesLe.lean#L37-L66

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

theorem Formalism.GaloisIrreducibility.card_residues_le_units (n D : ℕ) [NeZero n] (hD : 0 < D) :
    ((Finset.range n).filter (fun x => x ^ D ≡ 1 [MOD n])).card ≤
      #{u : (ZMod n)ˣ | u ^ D = 1} := by sorry
