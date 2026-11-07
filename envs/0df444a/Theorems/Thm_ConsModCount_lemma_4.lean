-- Prove2me | Theorems.Thm_ConsModCount_lemma_4
-- name    : ConsModCount.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T07:28:52.366723+00:00
-- url     : https://prove2.me/theorems/e05031c0-970b-48a8-a399-7a2de843b3fb
-- title:
--   Lemma 4 — count-preserving normal form with bounded, SI auxiliary domains
-- statement:
--   Let $m$ be a conservative minority operation on a finite set $D$, and let $R\subseteq A_1\times\cdots\times A_k$ be preserved by $m$, with nonempty $A_i\subseteq D$ and $d=\max_i|A_i|$. Then $R$ has a definition with introduced variables, using unary subsets, graphs of surjective homomorphisms, graphs of isomorphisms and relations $\mathrm{Lin}_C$, such that
--
--   1. the definition has unique extension: every tuple of $R$ has exactly one satisfying assignment of the introduced variables, and every tuple of $\prod_i A_i$ outside $R$ has none;
--   2. every actual domain of an introduced variable, every domain and image of a graph, and every ambient $C$ of a $\mathrm{Lin}_C$ atom has at most $d$ elements;
--   3. if every free-coordinate algebra $A_i$ of size $d$ is SI, then every introduced variable whose domain has size $d$ has an SI domain.
--
--   Unique extension makes the normal form preserve counts and weighted sums; the size bounds drive the domain descent of Theorem 2.
--
--   Differences from the source:
--   - reading: All actual domains and all ambient C in the definition have size at most d → the domains of the introduced variables, the domain and image of every graph atom, and the ambient C of every Lin_C atom have at most d elements; reason: the graphs' domains and images are the actual domains of their coordinates (proof, p.5: "every actual auxiliary domain and every ambient parity algebra")
--   - encoding: For any fixed finite family of bounded-arity relations, these definitions have fixed finite size → not a separate clause: the definition is a finite object (finitely many introduced variables and atoms); reason: a Lean definition object is finite; the sentence records this
--   - encoding: d = max_i |A_i| → d = sup of |A_i| over i (0 when k = 0); reason: the maximum of a finite family; k = 0 is not excluded by the source
--   - generalization: D is the nonempty domain of the template (p.1) → any finite D; reason: D is nonempty as soon as k ≥ 1 (the A_i are nonempty), and at k = 0 the statement concerns only the empty tuple, so it specializes to the source's on every nonempty D
-- source:
--   Xie, Conservative Modular Counting at Every Odd Prime, STOC 2027 submission (manuscript sha256 c673b4cc58550963462480168a22eca7184c16aebf1faa02497d68c5a46d876a), §3, Lemma 4, p.4 (PDF p.5); unique extension p.4 (PDF p.5); (3) p.3 (PDF p.4)

import Definitions.Def_ConsModCount_NormalForm

set_option autoImplicit false

namespace ConsModCount

/-- **Lemma 4 (count-preserving normal form)** (Xie, *Conservative Modular Counting at Every Odd Prime*, STOC 2027 submission (manuscript sha256 c673b4cc…), §3, p.4, PDF p.5). Fix a conservative minority
algebra `(D; m)` and an invariant relation `R ⊆ A₁ × ⋯ × A_k` with nonempty coordinate domains,
and let `d = maxᵢ |Aᵢ|`. Then `R` has a unique-extension definition using unary subsets,
surjective homomorphism graphs, isomorphism graphs and relations `Lin_C`; all actual domains and
all ambient `C` in the definition have size at most `d`; and if all size-`d` free-coordinate
algebras are SI, every introduced size-`d` auxiliary algebra is SI.

**Formalization Note.** Subalgebras of `(D; m)` are subsets (`m` is conservative). The definition is
an `NFDef`: introduced variables with actual domains `dom j` and atoms of the four kinds, each of the
allowed kind (`NFAtom.WF`). The bound `≤ d` is imposed on every introduced variable's domain and on
every set occurring in an atom (the domain and image of each graph, the ambient `C` of each
`Lin_C`). The paper's last sentence ("for any fixed finite family of bounded-arity relations, these
definitions have fixed finite size") holds of every `NFDef`, a finite object. `d` is
`Finset.univ.sup (|Aᵢ|)` (`0` when `k = 0`). -/
theorem lemma_4 {D : Type} [Fintype D] [DecidableEq D] (m : D → D → D → D)
    (hmin : IsMinority m) (hcons : IsConservativeOp m) {k : ℕ} (A : Fin k → Set D)
    (hA : ∀ i, (A i).Nonempty) (R : Set (Fin k → D)) (hRA : ∀ a ∈ R, ∀ i, a i ∈ A i)
    (hinv : Preserves (ternary m) R) :
    ∃ Φ : NFDef D k, Φ.UniquelyDefines A R ∧ (∀ at' ∈ Φ.atoms, at'.WF m) ∧
      (∀ j, (Φ.dom j).ncard ≤ Finset.univ.sup (fun i => (A i).ncard)) ∧
      (∀ at' ∈ Φ.atoms, at'.SetsBounded (Finset.univ.sup (fun i => (A i).ncard))) ∧
      ((∀ i, (A i).ncard = Finset.univ.sup (fun i => (A i).ncard) → IsSI m (A i)) →
        ∀ j, (Φ.dom j).ncard = Finset.univ.sup (fun i => (A i).ncard) → IsSI m (Φ.dom j)) := by sorry

end ConsModCount
