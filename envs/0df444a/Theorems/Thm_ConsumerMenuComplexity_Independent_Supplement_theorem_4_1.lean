-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_Supplement_theorem_4_1
-- name    : ConsumerMenuComplexity.Independent.Supplement.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T03:04:44.284461+00:00
-- url     : https://prove2.me/theorems/f71d66e1-0417-41f5-ab8e-fd4a91b039fe
-- title:
--   Theorem 4.1 — Tight finite correlated menu lower bound
-- statement:
--   For each integer $T\ge3$, there are a joint probability distribution $D$ over the two nonnegative real item values $v=(v_1,v_2)$ and ex-ante allocation caps $\alpha=(\alpha_1,\alpha_2)\in[0,1]^2$ such that the support of $D$ is finite with exactly $T$ types and utility optimality under these caps is attained. Every utility-optimal mechanism $M$ for this same $D$ and these same caps satisfies
--
--   $$
--   \left|\{(x_1^M(v),x_2^M(v),p^M(v)):v\in\operatorname{support}(D)\}\setminus\{(0,0,0)\}\right|\ge T.
--   $$
--
--   Here a mechanism assigns allocation probabilities $x_1^M,x_2^M$ and payment $p^M$ at every nonnegative type. Competitors range over all Borel measurable, incentive-compatible, individually rational unit-demand mechanisms with nonnegative payments, $0\le x_j^M\le1$ and $x_1^M+x_2^M\le1$. The cap constraints are $\mathbb E_D[x_j^M]\le\alpha_j$, and the objective is $\mathbb E_D[v_1x_1^M+v_2x_2^M-p^M]$. Ties may be resolved by any admissible selection; the lower bound holds for every optimum. The joint prior may have correlated coordinates.
--
--   This companion theorem establishes the tight finite-support utility menu lower bound. It is independent of the mission's infinite-menu goal for independent values. The selected option set is finite because it is the image of a finite support with the null option removed.
--
--   Differences from the source:
--   - encoding: integers T ≥ 3 → natural numbers T with 3 ≤ T; reason: the index ranges are identical
--   - encoding: a correlated distribution over two nonnegative real item values with support size T → a joint Borel probability measure on Fin 2 → ℝ≥0 with finite topological support of ncard T; reason: this uses the published arbitrary joint-prior model; no independence is imposed
--   - encoding: every utility-optimal mechanism, with an optimum constructed in the proof → existence of a utility-optimal mechanism and the lower bound for every utility-optimal mechanism; reason: the proof on PDF p. 14 establishes attainment, which is made explicit to exclude a vacuous universal claim
--   - encoding: at least T distinct non-null menu options → an embedding of Fin T into allocation/payment triples selected on the prior support, excluding the null triple; reason: an embedding expresses the same finite cardinality lower bound without an infinite-set ncard default
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, Theorem 4.1, PDF p. 10 (printed p. 9); proof PDF p. 14 (printed p. 13); standing model §§2–3, PDF pp. 6–10.

import Definitions.Def_ConsumerMenuComplexity_Independent_Mechanisms
open MeasureTheory

namespace ConsumerMenuComplexity.Independent.Supplement

/-- Goldner–Mohan–Phung, November 3, 2026 preprint, Theorem 4.1,
PDF p. 10 (printed p. 9); attainment is established in the proof on PDF p. 14.
SHA-256: 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4.
The prior is an arbitrary joint law, and competitors are all admissible mechanisms.
The embedding counts distinct selected non-null allocation/payment triples. -/
theorem theorem_4_1 (T : ℕ) (hT : 3 ≤ T) :
    ∃ D : Measure TypeSpace, IsProbabilityMeasure D ∧
      (priorSupport D).Finite ∧ (priorSupport D).ncard = T ∧
      ∃ α : Fin 2 → ℝ, ValidCaps α ∧
        (∃ M : Mechanism, UtilityOptimal D α M) ∧
        ∀ M : Mechanism, UtilityOptimal D α M →
          ∃ e : Fin T ↪ Option, ∀ i, e i ∈ nonNullOptions D M := by sorry

end ConsumerMenuComplexity.Independent.Supplement
