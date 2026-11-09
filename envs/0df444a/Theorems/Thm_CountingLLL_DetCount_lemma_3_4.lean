-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_3_4
-- name    : CountingLLL.DetCount.lemma_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:12.530229+00:00
-- url     : https://prove2.me/theorems/252c7bb1-d9cb-4a5e-ba0c-df467f9eb4ae
-- title:
--   Lemma 3.4 — canonical 2-tree inversion
-- statement:
--   Let $\mathcal E$ be a constraint set of a CSP formula and $c_0\in\mathcal E$. For every $T\in\mathfrak T_{\mathcal E,c_0}$,
--   $$\{\mathcal D\subseteq\mathcal E\mid c_0\in\mathcal D,\ \mathrm{Tree}(\mathcal D)=T\}=\{S\cup T\mid S\subseteq\mathrm{free}(T)\},$$
--   where $\mathrm{free}(T)=\mathcal E\setminus(T\cup R(T))$ and $R(T)$ is the final rejected set of Algorithm 1 on input $T$.
--
--   The free constraints are exactly the degrees of freedom of the preimage of $T$; this is the combinatorial core of the 2-tree expansion.
--
--   Differences from the source:
--   - encoding: a constraint set C (vertex set of G(C)) → a subfamily E of the constraint indices Fin m of a formula Φ; G(E) lives on Fin m with the constraints outside E isolated; reason: every constraint set is the full family of some formula; walks between members of E stay inside E
--   - encoding: an arbitrary fixed ordering of the constraints (lowest index in Algorithm 1) → the order of the index type Fin m; reason: the index order is an arbitrary fixed ordering; every ordering arises by relabelling the constraints
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Lemma 3.4, PDF p. 10 (printed p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Lemma 3.4 (Canonical 2-tree inversion): for a constraint set `E`, `c₀ ∈ E` and every
`T ∈ 𝔗_{E,c₀}`, `{D ⊆ E | c₀ ∈ D, Tree(D) = T} = {S ∪ T | S ⊆ free(T)}`. -/
theorem lemma_3_4 (Φ : CSP) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m) (hc₀ : c₀ ∈ E)
    (T : Finset (Fin Φ.m)) (hT : T ∈ Φ.twoTrees E c₀) :
    {D : Finset (Fin Φ.m) | D ⊆ E ∧ c₀ ∈ D ∧ Φ.Tree E c₀ D = T} =
      {D : Finset (Fin Φ.m) | ∃ S ⊆ Φ.free E c₀ T, D = S ∪ T} := by sorry

end CountingLLL.DetCount
