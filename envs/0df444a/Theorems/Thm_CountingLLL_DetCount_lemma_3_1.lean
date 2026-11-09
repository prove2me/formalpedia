-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_3_1
-- name    : CountingLLL.DetCount.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:47:12.446205+00:00
-- url     : https://prove2.me/theorems/333a12bd-011c-4b0c-ba19-37db07bf07cf
-- title:
--   Lemma 3.1 — $0\le r_{\mathcal C,c_0}\le 1.2p$
-- statement:
--   Let $\Phi$ satisfy Condition 1.1, $4\mathrm e\,p(D+1)^2\le1$, with $p$ its violation probability and $D$ its dependency degree. For every family $\mathcal E$ of constraints of $\Phi$ and every $c_0\in\mathcal E$,
--   $$0\le r_{\mathcal E,c_0}\le 1.2\,p,\qquad r_{\mathcal E,c_0}=1-\frac{Z(\mathcal E)}{Z(\mathcal E\setminus\{c_0\})}.$$
--   For $\mathcal E=\mathcal C$ this is Lemma 3.1.
--
--   It is the a priori range of the marginals estimated by the algorithm.
--
--   Differences from the source:
--   - generalization: the constraint set C of a formula satisfying Condition 1.1, with its own p and D → every constraint family E of a formula Φ satisfying Condition 1.1, graphs and 2-trees computed in G(E), with p and D the parameters of Φ; reason: E = all constraints is the source statement; the proofs of Lemma 4.3 and Theorem 1.2 apply the result to subfamilies with the parent bounds (PDF 14)
--   - generalization: standing assumption q ≥ 2, k ≥ 2, D ≥ 1 (PDF 3) → not assumed; reason: the statement and its proof do not use it, and recursive subfamilies may have width 1 or degree 0; instances satisfying it are covered
--   - encoding: uniform product measure P on Q and P[A | B] → counting ratio |{σ : A σ}| / |Q| and P[A ∧ B] / P[B]; reason: the same measure on a finite product; every conditioning event in the statement has positive probability under its hypotheses
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Lemma 3.1, PDF p. 8 (printed p. 7); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_CSP

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Lemma 3.1, uniformly over subfamilies: if `Φ` satisfies Condition 1.1 with violation
probability `p`, then for every constraint family `E` of `Φ` and every `c₀ ∈ E`,
`0 ≤ r_{E,c₀} ≤ 1.2 p` (`E = univ` is the paper's statement). -/
theorem lemma_3_1 (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (hc₀ : c₀ ∈ E) :
    0 ≤ Φ.r E c₀ ∧ Φ.r E c₀ ≤ 1.2 * Φ.pmax := by sorry

end CountingLLL.DetCount
