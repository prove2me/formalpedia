-- Prove2me | Theorems.Thm_DynLZ77_KK_local_sparse
-- name    : DynLZ77.KK.local_sparse
-- status  : Open
-- author  : @shaygo
-- created : 2026-11-25T05:08:11.470579+00:00
-- url     : https://prove2.me/theorems/7b2cf4ab-8485-4de4-aa98-b20b42b50fcc
-- title:
--   Kempa–Kociumaka Fact 8.9, localized: some identifier puts $O(|I|)$ synchronizing positions within $11\tau$ of $I$
-- statement:
--   There is a universal constant $C$ such that for every string $T[1..n]$ over any alphabet, every set of positions $I\subseteq[1..n]$ and every $\tau\in[1..\lfloor n/2\rfloor]$, some identifier $\mathrm{id}$ makes Construction 8.1 of Kempa and Kociumaka place few positions near $I$:
--   $$
--   \bigl|\{\,x\in S_{\mathrm{id}}:\ |x-i|\le 11\tau \text{ for some } i\in I\,\}\bigr|\;\le\; C\,|I| .
--   $$
--   Here $S_{\mathrm{id}}$ is the set of Construction 8.1 (definition `DynLZ77_KK_SyncConstruction`): with $Q$ the positions whose length-$\tau$ fragment has period at most $\tau/3$, a position $i\in[1..n-2\tau+1]$ belongs to $S_{\mathrm{id}}$ when the smallest identifier of a fragment starting in $[i..i+\tau]\setminus Q$ is that of $T[i..i+\tau)$ or of $T[i+\tau..i+2\tau)$.
--
--   This is the size bound of Fact 8.9 of the source (some identifier gives $|S_{\mathrm{id}}|\le 18n/\tau$), localized to the $11\tau$-neighbourhood of $I$, which consists of at most $(22\tau+1)|I|$ positions. It is the one ingredient of Lemma 8.4 of Boneh, Fried, Golan and Kraus (*Dynamic LZ77: No Space for Improvement*, $I$-local $\tau$-synchronizing sets of size $O(|I|)$) that depends on the choice of identifier; consistency, density and locality hold for every identifier.
--
--   **Formalization Note.** The constant $C$ is fixed before the alphabet, $T$, $I$ and $\tau$. The identifier is any function from strings to natural numbers; "within distance $11\tau$" is written as $i\le x+11\tau$ and $x\le i+11\tau$ with natural numbers.
-- source:
--   D. Kempa, T. Kociumaka, String Synchronizing Sets: Sublinear-Time BWT Construction and Optimal LCE Data Structure, STOC 2019, https://arxiv.org/abs/1904.04228 (v2), Section 8, Fact 8.9 (localized to the 11τ-neighbourhood of I); used for Boneh, Fried, Golan, Kraus, Dynamic LZ77: No Space for Improvement, Lemma 8.4 (p. 48)

import Mathlib.Data.Real.Basic
import Definitions.Def_DynLZ77_KK_SyncConstruction

set_option autoImplicit false

namespace DynLZ77.KK

open DynLZ77.Main

/-- **Sparse identifiers, localized** ([KK19, Construction 8.1 and Fact 8.9], localized to the
`11τ`-neighbourhood of a set `I`). There is a universal constant `C` such that for every string
`T[1..n]`, every `I ⊆ [1..n]` and every `τ ∈ [1..⌊n/2⌋]` some identifier makes Construction 8.1
put at most `C·|I|` positions within distance `11τ` of `I`. -/
theorem local_sparse : ∃ C : ℝ, ∀ {α : Type} [DecidableEq α] (T : List α) (I : Finset ℕ) (τ : ℕ),
    I ⊆ Finset.Icc 1 T.length → 1 ≤ τ → τ ≤ T.length / 2 →
      ∃ id : List α → ℕ,
        (((syncSet T τ id).filter (fun x => ∃ i ∈ I, i ≤ x + 11 * τ ∧ x ≤ i + 11 * τ)).card : ℝ)
          ≤ C * (I.card : ℝ) := by sorry

end DynLZ77.KK
