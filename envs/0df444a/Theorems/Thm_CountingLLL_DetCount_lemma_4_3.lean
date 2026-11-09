-- Prove2me | Theorems.Thm_CountingLLL_DetCount_lemma_4_3
-- name    : CountingLLL.DetCount.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:48:07.954751+00:00
-- url     : https://prove2.me/theorems/1fd78d89-8cff-462b-9570-ecd2f98b89ac
-- title:
--   Lemma 4.3 — accuracy of the marginal estimator
-- statement:
--   Let $\Phi$ satisfy Condition 1.1 with violation probability $p$. For every family $\mathcal E$ of constraints of $\Phi$, every $c_0\in\mathcal E$, every truncation budget $L\ge0$ and every choice of the enumerations in (20),
--   $$-2p\le\hat r^{(L)}_{\mathcal E,c_0}\le2p,\qquad\big|\hat r^{(L)}_{\mathcal E,c_0}-r_{\mathcal E,c_0}\big|\le4\cdot(0.9)^L.$$
--
--   With $L=\lceil\log_{1.1}(40m/\varepsilon)\rceil$ this gives the accuracy part of Theorem 1.2.
--
--   Differences from the source:
--   - generalization: the constraint set C of a formula satisfying Condition 1.1, with its own p and D → every constraint family E of a formula Φ satisfying Condition 1.1, graphs and 2-trees computed in G(E), with p and D the parameters of Φ; reason: E = all constraints is the source statement; the proofs of Lemma 4.3 and Theorem 1.2 apply the result to subfamilies with the parent bounds (PDF 14)
--   - generalization: standing assumption q ≥ 2, k ≥ 2, D ≥ 1 (PDF 3) → not assumed; reason: the statement and its proof do not use it, and recursive subfamilies may have width 1 or degree 0; instances satisfying it are covered
--   - generalization: the estimator (20) built with the enumerations of Lemma 3.5 → the estimator for every enumeration choice that enumerates E ∖ ({c₀} ∪ free(T)) for each 2-tree; reason: the source leaves the enumeration arbitrary; every choice, including the index order used by the algorithm, is covered
--   - encoding: an arbitrary fixed ordering of the constraints (lowest index in Algorithm 1) → the order of the index type Fin m; reason: the index order is an arbitrary fixed ordering; every ordering arises by relabelling the constraints
--   - encoding: uniform product measure P on Q and P[A | B] → counting ratio |{σ : A σ}| / |Q| and P[A ∧ B] / P[B]; reason: the same measure on a finite product; every conditioning event in the statement has positive probability under its hypotheses
--   - encoding: finite variables V and finite domains Q_v → V = Fin n and Q_v = Fin (q v), with q v ≥ 2; reason: every finite source variable space is relabelled bijectively; no constraint function or scope is restricted
--   - generalization: a finite set of constraints C → constraints indexed by Fin m, permitting equal scopes and predicates at different indices; reason: enumerating a source constraint set gives an instance with distinct indices; allowing repetitions preserves that full source case
-- source:
--   Hongyang Liu, Chunyang Wang, Yitong Yin, Yiyao Zhang, Can Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 submission #442 (October 2026), Lemma 4.3, PDF p. 14 (printed p. 13); https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_DetCount_Expansion

set_option autoImplicit false

namespace CountingLLL.DetCount

open CSP

/-- Lemma 4.3 (Accuracy of the marginal estimator), uniformly over the constraint families `E`
of a formula `Φ` satisfying Condition 1.1 (with `p` the violation probability of `Φ`): for every
`c₀ ∈ E`, every truncation budget `L ≥ 0` and every enumeration choice used in (20),
`−2p ≤ r̂^{(L)}_{E,c₀} ≤ 2p` and `|r̂^{(L)}_{E,c₀} − r_{E,c₀}| ≤ 4 · (0.9)^L`. -/
theorem lemma_4_3 (Φ : CSP) (hΦ : Φ.Condition11) (E : Finset (Fin Φ.m)) (c₀ : Fin Φ.m)
    (hc₀ : c₀ ∈ E) (L : ℕ) (en : Φ.EnumChoice) (hen : Φ.ValidEnum en) :
    -2 * Φ.pmax ≤ Φ.rhatWith en L E c₀ ∧ Φ.rhatWith en L E c₀ ≤ 2 * Φ.pmax ∧
      |Φ.rhatWith en L E c₀ - Φ.r E c₀| ≤ 4 * (0.9 : ℝ) ^ L := by sorry

end CountingLLL.DetCount
