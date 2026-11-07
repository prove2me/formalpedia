-- Prove2me | Theorems.Thm_DynStrings_fact_4_9_local_consistency
-- name    : DynStrings.fact_4_9_local_consistency
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:34.728426+00:00
-- url     : https://prove2.me/theorems/8ae2ea27-f505-4246-af30-2ab71f30f7cf
-- title:
--   Fact 4.9 — local consistency: boundaries and phrases are determined by a window of radius $O(\ell_k)$
-- statement:
--   Let $S$ be a string of length $n$, fix any choice of the orders, and let $k,m,\alpha\ge0$ be integers with $\alpha\ge\lfloor8\ell_k\rfloor$. Let $i,i'\in[m+2\alpha..n-\alpha]$ satisfy
--
--   $$S(i-m-2\alpha..i+\alpha]=S(i'-m-2\alpha..i'+\alpha].$$
--
--   If $i\in B_k$, then $i'\in B_k$. Moreover, if $S(i-m..i]$ is a level-$k$ phrase, then so is $S(i'-m..i']$, and both are represented by the same symbol.
--
--   Whether a cut is a level-$k$ boundary depends only on the text within distance $O(\ell_k)$ of it. This is the property that makes the grammars of different strings share their symbols.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: every choice of the orders → every family `lt` with `IsOrderFamily lt` (strict total orders on all syntactic symbols for even k ≥ 2, paused before active); reason: the parse reads only well-formed symbols, so orders on the larger syntactic type restrict to exactly the source's orders
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Fact 4.9, p.18 (cited from KNO24, Lemma 3.7)

import Mathlib
import Definitions.Def_DynStrings_Parse

namespace DynStrings

/-- **Fact 4.9** (local consistency, cited from [KNO24, Lemma 3.7]), p.18.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

Let `S` be a string of length `n`, fix a choice of the orders, and let `k, m, a ≥ 0` be integers
with `a ≥ ⌊8ℓ_k⌋` (the paper's `α`). Let `i, i' ∈ [m + 2a .. n − a]` satisfy
`S(i − m − 2a .. i + a] = S(i' − m − 2a .. i' + a]`. If `i ∈ B_k`, then `i' ∈ B_k`. Moreover, if
`S(i − m .. i]` is a level-`k` phrase, then so is `S(i' − m .. i']`, and both are represented by
the same symbol.

**Formalization Note.** `i ≤ n − a` is written `i + a ≤ n`. -/
theorem fact_4_9_local_consistency {α : Type} [DecidableEq α] (S : List α)
    (lt : ℕ → StrSym α → StrSym α → Prop) (hlt : IsOrderFamily lt) (k m a : ℕ)
    (ha : ⌊8 * ell k⌋₊ ≤ a) (i i' : ℕ) (hi : m + 2 * a ≤ i) (hin : i + a ≤ S.length)
    (hi' : m + 2 * a ≤ i') (hin' : i' + a ≤ S.length)
    (heq : frag S (i - m - 2 * a) (i + a) = frag S (i' - m - 2 * a) (i' + a)) :
    (i ∈ boundaries lt S k → i' ∈ boundaries lt S k) ∧
    ∀ A : StrSym α, IsPhrase lt S k (i - m) i A → IsPhrase lt S k (i' - m) i' A := by sorry

end DynStrings
