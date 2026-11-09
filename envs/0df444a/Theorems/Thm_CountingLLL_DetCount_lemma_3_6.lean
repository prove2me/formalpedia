-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_3_6
-- name    : CountingLLL.DetCount.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:15.021184+00:00
-- url     : https://prove2.me/theorems/41f691f7-3546-4895-8be8-421d8b9fc368
-- title:
--   Lemma 3.6 — correlation decay for the 2-tree expansion
-- statement:
--   Let $\Phi$ satisfy Condition 1.1 with parameters $p$ and $D$, let $\mathcal E$ be a family of its constraints and $c_0\in\mathcal E$. Put
--   $$\alpha=2.1(D+1)^2,\qquad\beta=p(1-2p)^{-(D+1)^2}.$$
--   Vectors $\boldsymbol x=(x_{\mathcal C^T_i,c^T_i})_{T\in\mathfrak T_{\mathcal E,c_0},\,1\le i\le\ell^T}$ are indexed by pairs $(T,i)$. Suppose every coordinate of $\boldsymbol x$ (and below also of $\boldsymbol y$) lies in $[-2p,2p]$.
--   1. (13) For every $T\in\mathfrak T_{\mathcal E,c_0}$,
--   $$\mathbb P\Big[\bigwedge_{c\in T}\neg c\;\Big|\;\mathrm{free}(T)\Big]\prod_{i=1}^{\ell^T}\frac{1}{1-x_{\mathcal C^T_i,c^T_i}}\le\beta^{|T|}.$$
--   2. (14) With $f$ the function (12),
--   $$|f(\boldsymbol x)-f(\boldsymbol y)|\le\alpha\sum_{T\in\mathfrak T_{\mathcal E,c_0}}(1.2\beta)^{|T|}\max_{1\le i\le\ell^T}\big|x_{\mathcal C^T_i,c^T_i}-y_{\mathcal C^T_i,c^T_i}\big|,$$
--   where the maximum over an empty index set is $0$.
--
--   This is the contraction that makes the truncated recursion accurate (Lemma 4.3).
--
--   Differences from the source:
--   - generalization: the constraint set C of a formula satisfying Condition 1.1, with its own p and D → every constraint family E of a formula Φ satisfying Condition 1.1, graphs and 2-trees computed in G(E), with p and D the parameters of Φ; reason: E = all constraints is the source statement; the proofs of Lemma 4.3 and Theorem 1.2 apply the result to subfamilies with the parent bounds (PDF 14)
--   - generalization: standing assumption q ≥ 2, k ≥ 2, D ≥ 1 (PDF 3) → not assumed; reason: the statement and its proof do not use it, and recursive subfamilies may have width 1 or degree 0; instances satisfying it are covered
--   - encoding: β = p(1 − 2p)^{−(D+1)²} → p / (1 − 2p)^{(D+1)²}; reason: equal, since 1 − 2p > 0 under Condition 1.1
--   - encoding: vectors x_{C^T_i, c^T_i} indexed by (T, i), 1 ≤ i ≤ ℓ^T → functions x T i of a constraint set T and a 0-based index i < ℓ^T; reason: same index set; coordinates of different 2-trees stay independent even when the pairs (C^T_i, c^T_i) coincide
--   - encoding: max over an empty index set interpreted as 0 → supremum in the nonnegative reals over range ℓ^T (0 when empty); reason: the source convention
--   - encoding: uniform product measure P on Q and P[A | B] → counting ratio |{σ : A σ}| / |Q| and P[A ∧ B] / P[B]; reason: the same measure on a finite product; every conditioning event in the statement has positive probability under its hypotheses
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Lemma 3.6, equations (13) and (14), PDF p. 11 (printed p. 10); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Lemma 3.6 (Correlation decay for the 2-tree expansion), uniformly over the constraint
families `E` of a formula `Φ` satisfying Condition 1.1, with `p, D` the parameters of `Φ`,
`α = 2.1(D+1)²` and `β = p(1 − 2p)^{−(D+1)²}`. Vectors are indexed by pairs `(T, i)`,
`x T i` standing for `x_{C^T_{i+1}, c^T_{i+1}}`, `i < ℓ^T`.
(13) For every `T ∈ 𝔗_{E,c₀}` and every `x` with all coordinates in `[−2p, 2p]`,
`P[⋀_{c∈T} ¬c | free(T)] ∏_{i=1}^{ℓ^T} 1/(1 − x_{C^T_i,c^T_i}) ≤ β^{|T|}`.
(14) For all such `x, y`,
`|f(x) − f(y)| ≤ α Σ_{T ∈ 𝔗_{E,c₀}} (1.2β)^{|T|} max_{1 ≤ i ≤ ℓ^T} |x_{C^T_i,c^T_i} − y_{C^T_i,c^T_i}|`,
the maximum over an empty index set being `0`. -/
theorem lemma_3_6 (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (hc₀ : c₀ ∈ E) :
    let p := Φ.pmax
    let α : ℝ := 2.1 * ((Φ.Dmax : ℝ) + 1) ^ 2
    let β : ℝ := p / (1 - 2 * p) ^ ((Φ.Dmax + 1) ^ 2)
    let Box : (Finset (Fin Φ.m) → ℕ → ℝ) → Prop := fun x =>
      ∀ T ∈ Φ.twoTrees E c₀, ∀ i < Φ.ell E c₀ T, -2 * p ≤ x T i ∧ x T i ≤ 2 * p
    (∀ T ∈ Φ.twoTrees E c₀, ∀ x, Box x →
      Φ.treeCoeff E c₀ T * ∏ i ∈ Finset.range (Φ.ell E c₀ T), 1 / (1 - x T i) ≤ β ^ T.card) ∧
    (∀ x y, Box x → Box y →
      |Φ.fvec E c₀ x - Φ.fvec E c₀ y| ≤
        α * ∑ T ∈ Φ.twoTrees E c₀, (1.2 * β) ^ T.card *
          (((Finset.range (Φ.ell E c₀ T)).sup (fun i => ‖x T i - y T i‖₊) : NNReal) : ℝ)) := by sorry

end CountingLLL.DetCount
