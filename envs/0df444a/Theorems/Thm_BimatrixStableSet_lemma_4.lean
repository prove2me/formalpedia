-- Prove2me | Theorems.Thm_BimatrixStableSet_lemma_4
-- name    : BimatrixStableSet.lemma_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:19:45.479672+00:00
-- url     : https://prove2.me/theorems/19360d7e-a790-456c-abaf-b1b7ae3fbf79
-- title:
--   Lemma 4 — a completely labeled vertex pair becomes $(0,0)$ of a game, with positive payoffs
-- statement:
--   Let $P_0$ be a simple $m$-polytope and $Q_0$ a simple $n$-polytope, each with $m+n$ facets labeled by $[m+n]$, and let $(x_0,y_0)$ be a completely labeled vertex pair of $P_0\times Q_0$. Then there is a game $(A',B')$ with best-response polytopes $P'$ and $Q'$ such that:
--
--   1. there are affine bijections $P_0\to P'$ and $Q_0\to Q'$ with a corresponding permutation of the labels that maps the facet labels of $P_0$ and $Q_0$ to those of $P'$ and $Q'$, with $(x_0,y_0)$ mapped to $(0,0)$, such that all completely labeled vertex pairs of $P_0\times Q_0$ are in bijection to those of $P'\times Q'$;
--   2. there are a game $(\hat A,\hat B)$ with all entries positive and bijective projective transformations $P'\to\hat P$ and $Q'\to\hat Q$ onto its best-response polytopes that leave the face lattices unchanged.
--
--   This reversal from polytopes to games lets a Nash equilibrium and the artificial equilibrium exchange roles, which the proof of Theorem 4 uses.
--
--   Differences from the source:
--   - encoding: labels in $[m+n]$ → the type `Fin m ⊕ Fin n`, with label $i\le m$ as `Sum.inl` and label $m+j$ as `Sum.inr`; reason: same labels, zero-based
--   - encoding: a simple polytope with $m+n$ labeled facets → a system with exactly one row per label, each row defining its own facet (`IsFacetLabeled`), in $\mathbb R^m$ resp. $\mathbb R^n$; reason: every such polytope has this description
--   - encoding: affine bijections $P\to P'$, $Q\to Q'$ → affine maps of the ambient space that restrict to bijections of the polytopes; reason: same content for full-dimensional polytopes
--   - reading: "by applying, if necessary, bijective projective transformations … all entries of $A'$ and $B'$ are positive" → there exist positive $\hat A,\hat B$ with projective label-preserving bijections $P'\to\hat P$, $Q'\to\hat Q$ of the form $z\mapsto(Mz+c)/(\langle w,z\rangle+\delta)$ with positive denominator, and with isomorphic face lattices; reason: the proof of (b) with display (4) has this form
-- source:
--   Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3, Lemma 4, p.8; display (4)

import Mathlib
import Definitions.Def_BimatrixStableSet_BestResponse
import Definitions.Def_BimatrixStableSet_PolytopeTypes

namespace BimatrixStableSet

variable {m n : ℕ}

/-- Lemma 4, p.8 (Ickstadt, Theobald, von Stengel, arXiv:2411.12385v3). Let `P₀` be a simple
`m`-polytope and `Q₀` a simple `n`-polytope, each with `m + n` facets labeled by `[m + n]`, and let
`(x₀, y₀)` be a completely labeled vertex pair. Then there is a game `(A', B')` with best-response
polytopes `P'`, `Q'` such that:
(a) there are affine bijections `P₀ → P'`, `Q₀ → Q'` and a permutation `π` of the labels mapping the
facet labels of `P₀`, `Q₀` to those of `P'`, `Q'`, with `(x₀, y₀)` mapped to `(0, 0)`, such that all
completely labeled vertex pairs of `P₀ × Q₀` are in bijection to those of `P' × Q'`;
(b) bijective projective transformations of `P'` and `Q'` that leave their face lattices unchanged
lead to a game `(Â, B̂)` with all entries positive.

**Formalization Note.** `P₀` and `Q₀` are systems with exactly one row for each label, each row
defining its own facet of a full-dimensional polytope (`IsFacetLabeled`). Every simple polytope with
`m + n` labeled facets has such a description. The affine bijections are affine maps of the ambient
space restricted to the polytopes. The clause on `π` is stated for all points, which is the meaning
of "maps the facet labels". -/
theorem lemma_4 (P₀ : System (Fin m ⊕ Fin n) m) (Q₀ : System (Fin m ⊕ Fin n) n)
    (hP₀ : (P₀.realize P₀.carrier).IsSimplePolytope m (m + n)) (hP₀' : IsFacetLabeled P₀)
    (hQ₀ : (Q₀.realize Q₀.carrier).IsSimplePolytope n (m + n)) (hQ₀' : IsFacetLabeled Q₀)
    (x₀ : Fin m → ℝ) (y₀ : Fin n → ℝ) (hxy : (x₀, y₀) ∈ completelyLabeledPairs P₀ Q₀) :
    ∃ A' B' : Matrix (Fin m) (Fin n) ℝ, HasBestResponsePolytopes A' B' ∧
      (∃ (f : (Fin m → ℝ) →ᵃ[ℝ] (Fin m → ℝ)) (g : (Fin n → ℝ) →ᵃ[ℝ] (Fin n → ℝ))
          (π : Equiv.Perm (Fin m ⊕ Fin n)),
        Set.BijOn f P₀.carrier (bestResponseP B').carrier ∧
        Set.BijOn g Q₀.carrier (bestResponseQ A').carrier ∧
        (∀ x ∈ P₀.carrier, ∀ l, l ∈ P₀.labels x ↔ π l ∈ (bestResponseP B').labels (f x)) ∧
        (∀ y ∈ Q₀.carrier, ∀ l, l ∈ Q₀.labels y ↔ π l ∈ (bestResponseQ A').labels (g y)) ∧
        f x₀ = 0 ∧ g y₀ = 0 ∧
        Set.BijOn (Prod.map f g) (completelyLabeledPairs P₀ Q₀)
          (completelyLabeledPairs (bestResponseP B') (bestResponseQ A'))) ∧
      (∃ Ahat Bhat : Matrix (Fin m) (Fin n) ℝ,
        (∀ i j, 0 < Ahat i j ∧ 0 < Bhat i j) ∧
        HasBestResponsePolytopes Ahat Bhat ∧
        IsProjectiveEquivalence (bestResponseP B') (bestResponseP Bhat) ∧
        IsProjectiveEquivalence (bestResponseQ A') (bestResponseQ Ahat)) := by sorry

end BimatrixStableSet
