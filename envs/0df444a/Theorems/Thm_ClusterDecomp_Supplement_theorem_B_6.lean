-- Prove2me | Theorems.Thm_ClusterDecomp_Supplement_theorem_B_6
-- name    : ClusterDecomp.Supplement.theorem_B_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T23:59:59.828185+00:00
-- url     : https://prove2.me/theorems/4e79ffb3-4d38-439a-95b1-d927442d4063
-- title:
--   Theorem B.6 — induced-subgraph spectral counterexample
-- statement:
--   Fix an integer $d\ge3$ and a constant $h\in(0,1]$ for which condition (21) has $d$-regular solutions for arbitrarily large $n$. Then $c^*>0$, and there are constants $C>0$ and $N$ such that, for every $n\ge N$, every $d$-regular graph $X$ satisfying (21), and every choice of distinct hosts in Definition B.2, the graph $G_n$ and its bipartition $P_1,P_2$ satisfy
--
--   $$
--   \lambda_2(L_{G_n[P_1]}),\ \lambda_2(L_{G_n[P_2]})\ge\frac{(c^*)^2}{2},
--   \qquad
--   \lambda_3(L_{G_n})\le\frac{C}{\sqrt n}.
--   $$
--
--   Consequently, for every fixed $c_0>0$, $2c_0\,3^6\lambda_3(L_{G_n})$ tends uniformly to zero along these graphs. Hence Lemma B.1 is false. Moreover, even on finite simple unweighted positive-degree graphs whose two parts each have at least two vertices and positive internal degree, there are no constants $\gamma>0$ and $C>0$ such that every bipartition obeys
--
--   $$
--   \min_{i=1,2}\lambda_2(L_{G[P_i]})\le C\lambda_3(L_G)^\gamma.
--   $$
--
--   This separates ordinary induced subgraphs from the degree-preserving subgraphs used by the repaired statement earlier in the paper.
--
--   Differences from the source:
--   - generalization: the chosen expander graph $X$ and hosts used to define each $G_n$ → every $d$-regular $X$ satisfying (21) and every injective host choice; reason: Propositions B.4 and B.5 use only regularity, (21), and distinct hosts, so the statement specializes to every family chosen by the source
--   - encoding: "for all sufficiently large $n$", $O(n^{-1/2})$, and convergence to zero → explicit threshold, absolute-bound, and epsilon quantifiers, all uniform over $X$ and the hosts; reason: this is the quantifier-explicit meaning of the three asymptotic clauses
--   - generalization: falsity for all graphs and the absence of a positive-power bound → falsity already on finite simple unweighted positive-degree graphs and bipartitions with positive-degree induced parts and in-range eigenvalues; reason: the constructed $G_n$ belong to this subclass, so negating the universal bound on the subclass is stronger and implies the source claim without invoking junk eigenvalue values
--   - encoding: $G[P_i]$ and $\lambda_k$ → weight restriction with no added loop and the one-indexed kth-smallest real root of the normalized-Laplacian characteristic polynomial; reason: this is exactly the paper's ordinary induced graph and eigenvalue convention
-- source:
--   Sun, Zhang, Zhou, Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee, STOC 2027 submission (manuscript sha256 ba091f54…), Theorem B.6 p.38 (PDF p.40), with eq. (21) and Definition B.2 p.36 (PDF p.38), Propositions B.4–B.5 p.37 (PDF p.39)

import Mathlib
import Definitions.Def_ClusterDecomp_Supplement_Gn
import Definitions.Def_ClusterDecomp_Supplement_LemmaB1

open Finset

namespace ClusterDecomp.Supplement

open ClusterDecomp

/-- **Theorem B.6 (counterexample to [OGT14, Lemma 1.1]).**

Sun, Zhang, Zhou, *Faster Cluster Decomposition with Stronger Bi-Criteria Guarantee*, STOC 2027
submission (manuscript sha256 ba091f54…), Theorem B.6, p.38 (PDF p.40), under the standing
choice of `d`, `h` and the expander family in (21), p.36 (PDF p.38).

For every fixed integer `d ≥ 3` and `h ∈ (0,1]` admitting infinitely many `d`-regular graphs
satisfying (21), the graphs `G_n` of Definition B.2 have, uniformly over the choice of the graph
`X` and the distinct hosts,

* `λ₂(L_{G_n[P_i]}) ≥ c*²/2` for both parts and all sufficiently large `n`;
* `λ₃(L_{G_n}) = O(n⁻¹⁄²)`, and hence `2 c₀ 3⁶ λ₃(L_{G_n}) → 0` for every fixed
  `c₀ > 0`.

Consequently Lemma B.1 is false. More strongly, there is no exponent `γ > 0` and universal
constant `C > 0` for which every graph and bipartition satisfies
`min_i λ₂(L_{G[P_i]}) ≤ C λ₃(L_G)^γ`.

**Formalization Note.**
* The first conjunct spells out "sufficiently large" as `∃ N, ∀ n ≥ N` and big-O as one
  `C > 0` quantified before `n`, `X` and the hosts. The second conjunct is the uniform epsilon
  definition of the displayed convergence to zero; `c₀` is quantified as the positive constant
  appearing in the refuted Lemma B.1.
* `X` ranges over every simple `d`-regular graph satisfying (21), and `x,y` over every injective
  choice of the `⌊√n⌋` hosts. This generalizes a fixed expander family, and the proof of
  Propositions B.4–B.5 uses only these hypotheses.
* The two negated universal bounds are restricted to finite simple unweighted positive-degree graphs
  and partitions whose induced parts have positive degree, with the eigenvalue indices in range.
  These are exactly the non-junk instances of `L_G`, `λ₃(L_G)` and `λ₂(L_{G[P_i]})`. Restricting
  the class inside a universally quantified claim makes its negation stronger; every `G_n` used by
  the counterexample belongs to this class.
* `G[P_i]` is the ordinary induced subgraph `induced G (P i)`, never the degree-preserving `G{P_i}`;
  the latter is the repaired statement proved earlier in the paper. -/
theorem theorem_B_6 :
    ∀ (d : ℕ) (h : ℝ), 3 ≤ d → 0 < h → h ≤ 1 → ExpanderFamily d h →
      0 < cStar d h ∧
      (∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (X : SimpleGraph (Fin n)), IsDRegular X d → Expands21 X d h →
          ∀ (x y : Fin (Nat.sqrt n) → Fin n), Function.Injective x → Function.Injective y →
            cStar d h ^ 2 / 2 ≤ lam (induced (Gn X x y) (P1 n)) 2 ∧
            cStar d h ^ 2 / 2 ≤ lam (induced (Gn X x y) (P2 n)) 2 ∧
            lam (Gn X x y) 3 ≤ C / Real.sqrt n) ∧
      (∀ c0 : ℝ, 0 < c0 → ∀ δ : ℝ, 0 < δ → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
        ∀ (X : SimpleGraph (Fin n)), IsDRegular X d → Expands21 X d h →
          ∀ (x y : Fin (Nat.sqrt n) → Fin n), Function.Injective x → Function.Injective y →
            2 * c0 * (3 : ℝ) ^ 6 * lam (Gn X x y) 3 ≤ δ) ∧
      ¬ LemmaB1 ∧
      ¬ ∃ γ : ℝ, 0 < γ ∧ ∃ C : ℝ, 0 < C ∧
        ∀ (V : Type) [Fintype V] [DecidableEq V] (G : WGraph V),
          IsUnweighted G → G.PosDeg → 3 ≤ Fintype.card V →
            ∀ P : Fin 2 → Finset V,
              (Pairwise fun i j => Disjoint (P i) (P j)) →
              (∀ v, ∃ i, v ∈ P i) →
              (∀ i, 2 ≤ (P i).card) →
              (∀ i, (induced G (P i)).PosDeg) →
              ∃ i, lam (induced G (P i)) 2 ≤ C * Real.rpow (lam G 3) γ := by sorry

end ClusterDecomp.Supplement
