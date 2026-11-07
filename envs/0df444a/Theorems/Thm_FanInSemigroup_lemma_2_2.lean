-- Prove2me | Theorems.Thm_FanInSemigroup_lemma_2_2
-- name    : FanInSemigroup.lemma_2_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T06:32:49.912807+00:00
-- url     : https://prove2.me/theorems/6d1f6479-985f-4b38-9085-9433033947ee
-- title:
--   Lemma 2.2 — a circuit for $S$ gives one for sum mod $k$
-- statement:
--   Let $S$ be a finite semigroup containing a nontrivial group, that is, not groupfree. Then there is a fixed modulus $m>1$ with the following property. For all injective encodings $e$ of $S$ by $k$ bits and $e'$ of the sum-zero mod $m$ semigroup by $k'$ bits there are constants $A,B$ such that for all $n\ge 1$, every circuit computing the $n$-fold product of $S$ under $e$ yields a circuit computing the $n$-fold product of the sum-zero mod $m$ semigroup under $e'$, with
--
--   $$
--   \mathrm{depth}(C')\le \mathrm{depth}(C)+A,\qquad \mathrm{size}(C')\le \mathrm{size}(C)+B\,n.
--   $$
--
--   The modulus depends on $S$ alone, and the constants do not depend on $n$ or on the circuit. With Theorem 2.3 this gives the direction from circuits to groupfree of the main theorem.
--
--   Differences from the source:
--   - reading: "any circuit for S" under a fixed encoding → every pair of injective encodings of S and of the target semigroup, with m chosen before them; reason: both directions of the construction work for any encoding
--   - encoding: "only a constant deeper and O(n) bigger" → depth ≤ depth + A and size ≤ size + B·n with A, B independent of n and C; reason: this is what the O-notation says at n ≥ 1
--   - encoding: the sum-zero mod k semigroup: {0,...,k−1} with ij = i + j mod k → Multiplicative (ZMod m); reason: the same semigroup; the page's k is called m because k counts bits here
--   - encoding: a directed acyclic graph with input nodes labelled by variables → gates in topological order, one input node per variable; reason: merging input nodes with the same label only lowers the size; no instance changes
-- source:
--   Chandra, Fortune, Lipton, Unbounded Fan-in Circuits and Associative Functions, STOC 1983, doi:10.1145/800061.808732, Lemma 2.2, p.54

import Definitions.Def_FanInSemigroup_HasConstDepthPolySize
import Definitions.Def_FanInSemigroup_IsGroupfree

set_option autoImplicit false

namespace FanInSemigroup

/-- **Lemma 2.2.** Chandra, Fortune, Lipton, STOC 1983, p.54: "Suppose semigroup S contains
nontrivial group G. Then any circuit for S can be transformed into a circuit for sum zero mod k,
some fixed k > 1, that is only a constant deeper and O(n) bigger than the original circuit."

**Formalization Note.** "contains nontrivial group" is `¬ IsGroupfree S`. The modulus `m` (the
page's `k`) comes before the encodings; the page's `k` bits are `k`, `k'` here. `A`, `B` depend on
the semigroup and the encodings, not on `n` or the circuit, and `B · n` is additive on top of the
given circuit's size. -/
theorem lemma_2_2 {S : Type*} [Semigroup S] [Finite S] (hS : ¬ IsGroupfree S) :
    ∃ m : ℕ, 1 < m ∧ ∀ {k k' : ℕ} (e : S → Fin k → Bool) (e' : Multiplicative (ZMod m) → Fin k' → Bool),
      Function.Injective e → Function.Injective e' →
      ∃ A B : ℕ, ∀ (n : ℕ) (hn : 1 ≤ n) (C : Circuit (Fin n × Fin k) (Fin k)),
        ComputesProduct e hn C →
        ∃ C' : Circuit (Fin n × Fin k') (Fin k'), ComputesProduct e' hn C' ∧
          C'.depth ≤ C.depth + A ∧ C'.size ≤ C.size + B * n := by sorry

end FanInSemigroup
