-- Prove2me | Theorems.Thm_ActiveLanguageGeneration_Hierarchy_Supplement_adversarial_stabilization
-- name    : ActiveLanguageGeneration.Hierarchy.Supplement.adversarial_stabilization
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T05:27:18.495486+00:00
-- url     : https://prove2.me/theorems/ebd443eb-31b5-4b99-96b0-358db49b4d54
-- title:
--   Lemma 3.10 — stabilisation of an adversarial generator
-- statement:
--   Let $U$ be a countably infinite universe and suppose a generator $G$ adversarially generates a collection $C$ in the limit with repetition. Then for every $K\in C$ and every full repetition-free enumeration $x_1,x_2,\ldots$ of $K$ there exist a finite list $a$ of distinct strings of $K$ and an integer $m\ge1$ such that $G(b)\in K$ for every finite list $b$ with
--
--   1. $b$ begins with $a$ (same entries, same order) and has at least one further entry;
--   2. the entries of $b$ are distinct strings of $K$;
--   3. $b$ contains $x_1,\ldots,x_m$, in any order.
--
--   Both $a$ and $m$ may depend on $K$ and on the enumeration. This is the stabilisation property on which the proof that $\mathrm{Adv}_{\mathrm R}\subseteq\mathrm{Adv}_{\mathrm{NR}}$ (Theorem 3.9) rests.
--
--   Differences from the source:
--   - encoding: countably infinite universe U (without loss of generality N) → an arbitrary type U with [Countable U] [Infinite U]; reason: this is the paper's standing assumption of §2; every such U is in bijection with N
--   - encoding: x1, …, xm → x 0, …, x (m − 1); reason: zero-based indexing of the enumeration
--   - encoding: b begins with a and has at least one further entry → a is a prefix of b (a <+: b) and a.length < b.length; reason: lists are histories, oldest entry first
-- source:
--   Debmalya Panigrahi, Fan Wei, Ian Zhang, STOC 2027 submission #1167 (October 2026), Language Generation Beyond Adversarial Examples, Lemma 3.10, printed p.15 (PDF p.16); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1167.pdf

import Definitions.Def_ActiveLanguageGeneration_Hierarchy_Supplement_Adversarial

set_option autoImplicit false

namespace ActiveLanguageGeneration.Hierarchy.Supplement

open ActiveLanguageGeneration.Hierarchy

/-- Lemma 3.10, printed p.15 (PDF p.16). Lists are oldest-first; "`b` begins with `a` and has
at least one further entry" is `a <+: b` with `a.length < b.length`; `x 0, …, x (m-1)` are the
paper's `x₁, …, x_m`. -/
theorem adversarial_stabilization (U : Type) [Countable U] [Infinite U]
    (C : LanguageCollection U) (G : Generator U) (hG : AdvGenerates .R G C) :
    ∀ K ∈ C, ∀ x : ℕ → U, IsEnumeration K x →
      ∃ a : List U, ∃ m : ℕ, 1 ≤ m ∧ a.Nodup ∧ (∀ u ∈ a, u ∈ K.val) ∧
        ∀ b : List U, a <+: b → a.length < b.length → b.Nodup →
          (∀ u ∈ b, u ∈ K.val) → (∀ j < m, x j ∈ b) → G b ∈ K.val := by sorry

end ActiveLanguageGeneration.Hierarchy.Supplement
