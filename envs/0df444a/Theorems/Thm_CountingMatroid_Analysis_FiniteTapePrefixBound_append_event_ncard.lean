-- Prove2me | Theorems.Thm_CountingMatroid_Analysis_FiniteTapePrefixBound_append_event_ncard
-- name    : CountingMatroid.Analysis.FiniteTapePrefixBound.append_event_ncard
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-24T11:25:16.47459+00:00
-- url     : https://prove2.me/theorems/b5283e57-bb96-428e-9bbf-a0b6c9a50f6f
-- title:
--   Deleting a fixed prefix preserves event cardinality
-- statement:
--   Let $m\in\mathbb N$, let $p$ be a Boolean list with $|p|\le m$, and let $E$ be any predicate on Boolean lists. With $p\preceq b$ meaning that $p$ is a prefix of $b$,
--
--   $$\bigl|\{b:|b|=m,\ p\preceq b,\ E(b)\}\bigr|=\bigl|\{s:|s|=m-|p|,\ E(p\mathbin{+\!+}s)\}\bigr|.$$
--
--   This is the event-cardinality form of removing a fixed consumed history.
-- source:
--   https://github.com/meelgroup/counting-matroid/blob/dd16a4628fdb095c58fe0f3dfd8e353c6e97443c/CountingMatroid/Analysis/FiniteTapePrefixBound.lean#L27-L48

import Mathlib.Data.ENNReal.Inv
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

/-!
Finite fair-bit conditioning by a consumed prefix. Appending a fixed prefix
is a bijection on its suffix event; disjoint consumed-prefix cylinders let
uniform suffix estimates transfer to the whole finite tape. This module
proves only counting facts, not the program's stopping-prefix property or
the phase's conditional analytic estimate.
-/

namespace CountingMatroid.Analysis.FiniteTapePrefixBound
end CountingMatroid.Analysis.FiniteTapePrefixBound
open CountingMatroid CountingMatroid.Analysis CountingMatroid.Analysis.FiniteTapePrefixBound

theorem CountingMatroid.Analysis.FiniteTapePrefixBound.append_event_ncard (m : ℕ) (pref : List Bool)
    (hlen : pref.length ≤ m) (E : List Bool → Prop) :
    Set.ncard {bits : List Bool | bits.length = m ∧ pref <+: bits ∧ E bits} =
      Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
        E (pref ++ suffix)} := by sorry
