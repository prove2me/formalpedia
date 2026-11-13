-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_3_5
-- name    : CountingLLL.DetCount.lemma_3_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:11.794108+00:00
-- url     : https://prove2.me/theorems/807f159c-3563-463e-a10c-b7517db9b405
-- title:
--   Lemma 3.5 — recursion through 2-tree expansion
-- statement:
--   Let $\Phi$ satisfy Condition 1.1, let $\mathcal E$ be a family of its constraints and $c_0\in\mathcal E$. For each $T\in\mathfrak T_{\mathcal E,c_0}$ enumerate $\mathcal E\setminus(\{c_0\}\cup\mathrm{free}(T))=\{c^T_1,\dots,c^T_{\ell^T}\}$, and let $\mathcal C^T_i=\mathrm{free}(T)\cup\{c^T_1,\dots,c^T_i\}$. Then
--   $$r_{\mathcal E,c_0}=\sum_{T\in\mathfrak T_{\mathcal E,c_0}}(-1)^{|T|-1}\,\mathbb P\Big[\bigwedge_{c\in T}\neg c\;\Big|\;\mathrm{free}(T)\Big]\prod_{i=1}^{\ell^T}\frac{1}{1-r_{\mathcal C^T_i,c^T_i}}.$$
--   The identity holds for every choice of the enumerations.
--
--   This exact recursion (9) is what the estimator (20) truncates.
--
--   Differences from the source:
--   - generalization: the constraint set C of a formula satisfying Condition 1.1, with its own p and D → every constraint family E of a formula Φ satisfying Condition 1.1, graphs and 2-trees computed in G(E), with p and D the parameters of Φ; reason: E = all constraints is the source statement; the proofs of Lemma 4.3 and Theorem 1.2 apply the result to subfamilies with the parent bounds (PDF 14)
--   - generalization: standing assumption q ≥ 2, k ≥ 2, D ≥ 1 (PDF 3) → not assumed; reason: the statement and its proof do not use it, and recursive subfamilies may have width 1 or degree 0; instances satisfying it are covered
--   - encoding: an enumeration {c^T_1, …, c^T_{ℓ^T}} for each T → for each T an injective map Fin ℓ^T → Fin m with values in E ∖ ({c₀} ∪ free(T)); position j holds c^T_{j+1}; reason: an injective map into a set of size ℓ^T is an enumeration of it; every enumeration is covered
--   - encoding: a constraint set C (vertex set of G(C)) → a subfamily E of the constraint indices Fin m of a formula Φ; G(E) lives on Fin m with the constraints outside E isolated; reason: every constraint set is the full family of some formula; walks between members of E stay inside E
--   - encoding: an arbitrary fixed ordering of the constraints (lowest index in Algorithm 1) → the order of the index type Fin m; reason: the index order is an arbitrary fixed ordering; every ordering arises by relabelling the constraints
--   - encoding: uniform product measure P on Q and P[A | B] → counting ratio |{σ : A σ}| / |Q| and P[A ∧ B] / P[B]; reason: the same measure on a finite product; every conditioning event in the statement has positive probability under its hypotheses
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Lemma 3.5, equation (9), PDF p. 10 (printed p. 9); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Lemma 3.5 (Recursion through 2-tree expansion), for every constraint family `E` of a formula
`Φ` satisfying Condition 1.1, every `c₀ ∈ E`, and every choice of enumerations: if for each
`T ∈ 𝔗_{E,c₀}` the map `e T` enumerates `E ∖ ({c₀} ∪ free(T)) = {c^T_1, …, c^T_{ℓ^T}}`
(position `j` holds `c^T_{j+1}`) and `C^T_{j+1} = free(T) ∪ {c^T_1, …, c^T_{j+1}}`, then
`r_{E,c₀} = Σ_{T ∈ 𝔗_{E,c₀}} (−1)^{|T|−1} P[⋀_{c∈T} ¬c | free(T)] ∏_{i=1}^{ℓ^T} 1/(1 − r_{C^T_i,c^T_i})`. -/
theorem lemma_3_5 (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (hc₀ : c₀ ∈ E)
    (e : (T : Finset (Fin Φ.m)) → Fin (Φ.ell E c₀ T) → Fin Φ.m)
    (he : ∀ T ∈ Φ.twoTrees E c₀, Function.Injective (e T) ∧ ∀ j, e T j ∈ Φ.rest E c₀ T) :
    Φ.r E c₀ = ∑ T ∈ Φ.twoTrees E c₀, (-1 : ℝ) ^ (T.card - 1) * Φ.treeCoeff E c₀ T *
      ∏ j : Fin (Φ.ell E c₀ T), 1 / (1 - Φ.r (Φ.prefixFam (Φ.free E c₀ T) (e T) j) (e T j)) := by sorry

end CountingLLL.DetCount
