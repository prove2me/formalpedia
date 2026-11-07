-- Prove2me | Theorems.Thm_DynStrings_lemma_4_7_creation_rounds_intrinsic
-- name    : DynStrings.lemma_4_7_creation_rounds_intrinsic
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:48.323195+00:00
-- url     : https://prove2.me/theorems/ca7b3c2e-fecc-4a59-bd5c-9b4cb9b0829e
-- title:
--   Lemma 4.7 — every nonterminal node labelled $A$ is created in round $\lambda(A)$
-- statement:
--   Let $S$ be a string and fix any choice of the orders. Let $v$ be a node of the parse tree $T(S)$ labelled by a nonterminal (a run or a tuple) $A$, that is, a fragment $S(x..y]$ that is a level-$k$ phrase represented by $A$ for some level $k$. Then $v$ is created in round $\lambda(A)$:
--
--   1. $S(x..y]$ is a level-$\lambda(A)$ phrase represented by $A$, and
--   2. $S(x..y]$ is not a level-$(\lambda(A)-1)$ phrase.
--
--   The round in which a nonterminal is formed depends only on the symbol, not on the string being parsed. This is what lets the analysis decide, level by level, whether a tuple of one string occurs in the grammar of another.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: every choice of the orders → every family `lt` with `IsOrderFamily lt` (strict total orders on all syntactic symbols for even k ≥ 2, paused before active); reason: the parse reads only well-formed symbols, so orders on the larger syntactic type restrict to exactly the source's orders
--   - reading: v is a symbol of S_{λ(A)} but not of S_{λ(A)−1} → the fragment of v is a level-λ(A) phrase represented by A and is not represented by any symbol of S_{λ(A)−1}; reason: the source identifies nodes with the fragments they represent (p.17), so a symbol of S_{λ(A)−1} representing the same fragment would be v itself
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Lemma 4.7, p.17

import Mathlib
import Definitions.Def_DynStrings_Parse

namespace DynStrings

/-- **Lemma 4.7** (creation rounds are intrinsic), p.17.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

For every string `S`, every choice of the orders, and every node of `T(S)` labelled by a
nonterminal `A` — a level-`k` phrase `S(x..y]` represented by `A`, for some level `k` — the node
is created in round `λ(A)`: `S(x..y]` is a level-`λ(A)` phrase represented by `A`, and it is not a
level-`(λ(A) − 1)` phrase.

**Formalization Note.** Nodes are identified with the fragments they represent (p.17). "Not a
symbol of `S_{λ(A)−1}`" is stated as: no symbol of `S_{λ(A)−1}` represents `S(x..y]`. -/
theorem lemma_4_7_creation_rounds_intrinsic {α : Type} [DecidableEq α] (S : List α)
    (lt : ℕ → StrSym α → StrSym α → Prop) (hlt : IsOrderFamily lt) (k x y : ℕ) (A : StrSym α)
    (hA : StrSym.IsNonterminal A) (hph : IsPhrase lt S k x y A) :
    IsPhrase lt S (StrSym.cr A) x y A ∧ ¬ ∃ B, IsPhrase lt S (StrSym.cr A - 1) x y B := by sorry

end DynStrings
