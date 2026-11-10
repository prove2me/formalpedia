-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_perfect_completeness
-- name    : BirthdayEntropy.Soundness.perfect_completeness
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:50:39.636202+00:00
-- url     : https://prove2.me/theorems/3a942187-4166-4d20-9e76-92cf2fab50be
-- title:
--   Lemma B.1 — Perfect completeness
-- statement:
--   Let $\varphi$ be any Boolean ternary CSP with indexed constraints, distinct variables in each scope and arbitrary predicates. For every $1\le\ell\le n$, if a global assignment satisfies every constraint, then
--   $$G_{\varphi,\ell}\text{ contains a clique of size }K=\binom n\ell.$$
--   This implication is independent of the NO-gap and occurrence promises. At $\ell=n$, $K=1$ and a singleton is a clique. This is the perfect-completeness component of Theorem 2.1.
--
--   Differences from the source:
--   - encoding: variables [n] and indexed constraints with arbitrary ternary Boolean predicates → Fin n, Fin m and the published RandOrderCSP.CSP 3 Bool with injective scope rows; reason: reindexing and ordering each three-element scope changes no instance or predicate; repeated scopes remain distinct indices
--   - encoding: a K-clique → a K-element finite set with adjacency for every two distinct members; reason: the same clique notion, including K=1
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma B.1, PDF pp22 / printed pp21

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Graph

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Lemma B.1, PDF p22 / printed p21. Completeness has no NO-gap
or bounded-occurrence hypothesis and includes K=1 at ell=n. -/
theorem perfect_completeness (n m : ℕ) (φ : CSP n m) (ℓ : ℕ)
    (hℓ : 1 ≤ ℓ) (hℓn : ℓ ≤ n) (hφ : Satisfiable φ) :
    HasTargetClique φ ℓ := by sorry

end BirthdayEntropy.Soundness
