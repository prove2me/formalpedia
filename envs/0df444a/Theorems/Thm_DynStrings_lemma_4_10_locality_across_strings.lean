-- Prove2me | Theorems.Thm_DynStrings_lemma_4_10_locality_across_strings
-- name    : DynStrings.lemma_4_10_locality_across_strings
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:54:34.361197+00:00
-- url     : https://prove2.me/theorems/2a8834ef-3781-45a0-9226-9faaf063a26c
-- title:
--   Lemma 4.10 — locality across two strings parsed with the same orders
-- statement:
--   Fix $k\ge0$, any choice of the orders, and two strings $U,V$ parsed with these orders. Let $a\le b$ and $a'\le b'$ be cuts of $U$ and $V$ with $b-a=b'-a'$, and suppose that for some integer $\alpha\ge\lfloor8\ell_k\rfloor$
--
--   $$U(a-2\alpha..b+\alpha]=V(a'-2\alpha..b'+\alpha],$$
--
--   where both fragments exist. Write $x'=a'+(x-a)$ for every cut $x$ of $U$.
--
--   1. For every $x\in[a..b]$, $x\in B_k(U)$ if and only if $x'\in B_k(V)$.
--   2. If $U(x..y]$ with $a\le x\le y\le b$ is a level-$k$ phrase of $U$, then $V(x'..y']$ is a level-$k$ phrase of $V$ represented by the same symbol.
--   3. In particular, both conclusions hold whenever $U(a-\mu_k..b+\mu_k]=V(a'-\mu_k..b'+\mu_k]$ (with both fragments existing), where $\mu_k=2\lfloor8\ell_k\rfloor$.
--
--   This transfers the parse from one string to another wherever their texts agree on a slightly larger window, which is how symbols of $X$ are found in the grammars of the collection.
--
--   Differences from the source:
--   - generalization: strings over a fixed countably infinite alphabet $\Sigma$ → strings over an arbitrary type $\alpha$ with decidable equality; reason: the statement holds for every alphabet type, and a countably infinite $\alpha$ gives the source's statement
--   - encoding: every choice of the orders → every family `lt` with `IsOrderFamily lt` (strict total orders on all syntactic symbols for even k ≥ 2, paused before active); reason: the parse reads only well-formed symbols, so orders on the larger syntactic type restrict to exactly the source's orders
--   - encoding: where both fragments exist → 2α ≤ a, b + α ≤ |U|, 2α ≤ a′, b′ + α ≤ |V| (μ_k on both sides in clause 3); reason: the fragments S(i..j] are defined exactly for cuts 0 ≤ i ≤ j ≤ |S|
-- source:
--   Duyster, Kociumaka, Komlós, Optimal Dynamic Strings in Compressed Space (manuscript, sha256 cfcb3de9…), Lemma 4.10, pp.18–19 (last sentence on p.19)

import Mathlib
import Definitions.Def_DynStrings_Parse

namespace DynStrings

/-- **Lemma 4.10** (locality across strings), pp.18–19.
Duyster, Kociumaka, Komlós, *Optimal Dynamic Strings in Compressed Space* (manuscript, sha256 cfcb3de9…)

Fix `k ≥ 0` and two strings `U, V`, parsed with the same choice of the orders. Let `a ≤ b` and
`a' ≤ b'` be cuts of `U` and `V` with `b − a = b' − a'`, and suppose that, for some integer
`r ≥ ⌊8ℓ_k⌋` (the paper's `α`), `U(a − 2r .. b + r] = V(a' − 2r .. b' + r]`, where both fragments
exist. Write `x' = a' + (x − a)`.
(a) For every `x ∈ [a..b]`, `x ∈ B_k(U)` iff `x' ∈ B_k(V)`.
(b) If `U(x..y]`, `a ≤ x ≤ y ≤ b`, is a level-`k` phrase of `U`, then `V(x'..y']` is a level-`k`
phrase of `V` represented by the same symbol.
In particular, the conclusions hold whenever `U(a − μ_k .. b + μ_k] = V(a' − μ_k .. b' + μ_k]`.

**Formalization Note.** "Both fragments exist" is `2r ≤ a`, `b + r ≤ |U|`, `2r ≤ a'`,
`b' + r ≤ |V|` (with `μ_k` in place of `2r` and `r` in the last clause). -/
theorem lemma_4_10_locality_across_strings {α : Type} [DecidableEq α] (U V : List α)
    (lt : ℕ → StrSym α → StrSym α → Prop) (hlt : IsOrderFamily lt) (k a b a' b' : ℕ)
    (hab : a ≤ b) (hab' : a' ≤ b') (hlen : b - a = b' - a') :
    (∀ r : ℕ, ⌊8 * ell k⌋₊ ≤ r → 2 * r ≤ a → b + r ≤ U.length → 2 * r ≤ a' →
      b' + r ≤ V.length → frag U (a - 2 * r) (b + r) = frag V (a' - 2 * r) (b' + r) →
      (∀ x, a ≤ x → x ≤ b → (x ∈ boundaries lt U k ↔ a' + (x - a) ∈ boundaries lt V k)) ∧
      (∀ x y (A : StrSym α), a ≤ x → x ≤ y → y ≤ b → IsPhrase lt U k x y A →
        IsPhrase lt V k (a' + (x - a)) (a' + (y - a)) A)) ∧
    (muk k ≤ a → b + muk k ≤ U.length → muk k ≤ a' → b' + muk k ≤ V.length →
      frag U (a - muk k) (b + muk k) = frag V (a' - muk k) (b' + muk k) →
      (∀ x, a ≤ x → x ≤ b → (x ∈ boundaries lt U k ↔ a' + (x - a) ∈ boundaries lt V k)) ∧
      (∀ x y (A : StrSym α), a ≤ x → x ≤ y → y ≤ b → IsPhrase lt U k x y A →
        IsPhrase lt V k (a' + (x - a)) (a' + (y - a)) A)) := by sorry

end DynStrings
