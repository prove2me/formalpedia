-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_3_2
-- name    : CountingLLL.DetCount.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:07.822247+00:00
-- url     : https://prove2.me/theorems/3dd7a531-80ba-47e5-bd25-e54d8d4bc7c6
-- title:
--   Lemma 3.2 — Algorithm 1 outputs 2-trees and fixes them
-- statement:
--   Let $\mathcal E$ be a constraint set of a CSP formula, $c_0$ a constraint, and $\mathrm{Tree}=\mathrm{Tree}_{\mathcal E,c_0}$ the output of Algorithm 1 in the dependency graph $G(\mathcal E)$. Then:
--   1. for every $\mathcal D$ with $c_0\in\mathcal D\subseteq\mathcal E$, $\mathrm{Tree}(\mathcal D)\in\mathfrak T_{\mathcal E,c_0}$;
--   2. for every $T\in\mathfrak T_{\mathcal E,c_0}$, $\mathrm{Tree}(T)=T$.
--
--   The canonical 2-tree map is thus onto $\mathfrak T_{\mathcal E,c_0}$, which is what lets the inclusion–exclusion sum (8) be regrouped by 2-trees.
--
--   Differences from the source:
--   - encoding: a constraint set C (vertex set of G(C)) → a subfamily E of the constraint indices Fin m of a formula Φ; G(E) lives on Fin m with the constraints outside E isolated; reason: every constraint set is the full family of some formula; walks between members of E stay inside E
--   - encoding: an arbitrary fixed ordering of the constraints (lowest index in Algorithm 1) → the order of the index type Fin m; reason: the index order is an arbitrary fixed ordering; every ordering arises by relabelling the constraints
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Lemma 3.2, PDF p. 9 (printed p. 8); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Lemma 3.2, for a constraint set `E` of `Φ` and a root `c₀`: for any `c₀ ∈ D ⊆ E`, the output
`Tree_{E,c₀}(D)` of Algorithm 1 belongs to `𝔗_{E,c₀}`; moreover every `T ∈ 𝔗_{E,c₀}` is a fixed
point, `Tree_{E,c₀}(T) = T`. -/
theorem lemma_3_2 (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) :
    (∀ D : Finset (Fin Φ.m), c₀ ∈ D → D ⊆ E → Φ.Tree E c₀ D ∈ Φ.twoTrees E c₀) ∧
    (∀ T ∈ Φ.twoTrees E c₀, Φ.Tree E c₀ T = T) := by sorry

end CountingLLL.DetCount
