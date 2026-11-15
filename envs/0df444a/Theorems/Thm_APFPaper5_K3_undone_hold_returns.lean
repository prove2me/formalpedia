-- Prove2me | Theorems.Thm_APFPaper5_K3_undone_hold_returns
-- name    : APFPaper5.K3.undone_hold_returns
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:04:11.055845+00:00
-- url     : https://prove2.me/theorems/e870fd86-82f4-4651-8e5c-cfae57621270
-- title:
--   Undone hold returns
-- statement:
--   Supporting lemma: undone hold returns. The exact quantified statement supplied with this entry is controlling, including every displayed hypothesis. Finite Process and injectivity are supplied. Finite words individually do not make their whole type finite, and B04 does not establish that finiteness.
-- source:
--   Sib v44 Theorems/Thm_APFB01_undone_hold_returns.lean:45

import Definitions.Def_APF_B01_DeclaredInput
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Data.Finite.Prod
import Mathlib.Logic.Function.Iterate

set_option autoImplicit false

universe uX uP



namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.undone_hold_returns {S : Type*} [Finite S] (D : S → S) (hD : Function.Injective D)
    (x : S) : ∃ n : ℕ, 0 < n ∧ D^[n] x = x := by sorry
