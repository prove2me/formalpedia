-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_lemma_5_4
-- name    : ConsumerMenuComplexity.Independent.lemma_5_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:07:10.014208+00:00
-- url     : https://prove2.me/theorems/c5cbd264-ef92-43e1-b706-18bcc30f62b7
-- title:
--   Lemma 5.4 — one free item-2 option improves L and each supply
-- statement:
--   A mechanism assigns allocation probabilities $x_1(v),x_2(v)$ and payment $p(v)$ to every type $v=(v_1,v_2)\in\mathbb R_{\ge0}^2$. It is admissible when the rules are Borel measurable, $0\le x_i\le1$, $x_1+x_2\le1$, $p\ge0$, and the buyer's utility $u^M(v)=v_1x_1(v)+v_2x_2(v)-p(v)$ is nonnegative and is at least the payoff from every other report. All mechanism comparisons below range over this entire admissible class.
--
--   For a prior $D$, write $U_D(M)=\mathbb E_D[u^M]$, $a_i^D(M)=\mathbb E_D[x_i^M]$, and $L_{D,(\lambda_1,\lambda_2)}(M)=U_D(M)-\lambda_1a_1^D(M)-\lambda_2a_2^D(M)$. A menu includes the null option, has feasible nonnegative-price triples, and is equipped with an actual utility-maximizing choice at every type.
--
--   Let $D_1$ be any probability law on the nonnegative reals, independently of $D_2=U(0,1)$; no density or finite mean is required. Fix $0<c<1$. Suppose $M$ selects from a valid menu $S$ containing only single-item lotteries. Put $d=u^M(0,1)$ and form $S^{\rm free}$ by keeping every item-1 option and replacing the item-2 options with $(0,d,0)$. The defined selected mechanism $M^{\rm free}$ is admissible, selects from $S^{\rm free}$, and this menu is structured with $0\le d\le1$. Moreover,
--   $$L_{D,(1,c)}(M)\le L_{D,(1,c)}(M^{\rm free}),\qquad a_i^D(M^{\rm free})\le a_i^D(M)\quad(i=1,2).$$
--   The tie rule preserves original item-1 choices when they remain maximal and takes the free option for original item-2 ties. The comparisons retain meaningful extended values when $D_1$ has infinite mean.
--
--   Differences from the source:
--   - encoding: two nonnegative real item values and truthful unit-demand mechanisms with nonnegative payments → Fin 2 coordinates in the nonnegative reals, the published raw mechanism defined at every report of the full orthant (also outside support(D)), IC/IR/NPT and unit-demand feasibility at all those reports, and Borel measurable allocation/payment rules; reason: coordinates 0 and 1 represent items 1 and 2; a truthful mechanism on the support extends to the orthant by the closure of its menu, without changing it on the support; a rule measurable only for the completed prior agrees a.e. with a Borel subgradient selection having the same utility, so no objective changes; no smoothness or finite-support restriction is imposed
--   - encoding: expected utility and modified expected utility minus allocation costs → nonnegative extended utility expectation and subtraction of the finite real expected allocation cost; ordinary real expected allocations; reason: admissibility bounds allocations on a probability space; this prevents a nonintegrable utility from defaulting to zero and retains infinite-mean priors where the source allows them
--   - encoding: the menu obtained by the stated replacement with the source tie convention → the computed free menu and complete selected mechanism, including d=0 and reports outside the second marginal support; reason: the replacement is constructed from M and retains its actual item-1 choices where needed; no unrelated replacement or supply inequality is assumed
--   - generalization: D1 has a density f1, with no condition on it → D1 is an arbitrary probability law on the nonnegative reals, atoms and infinite mean allowed; reason: every law with a density is such a law, so the source claim is the special case
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Lemma 5.4, PDF p.19 (printed p.18)

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Transforms
import Definitions.Def_ConsumerMenuComplexity_Independent_Construction
open MeasureTheory
open scoped NNReal

namespace ConsumerMenuComplexity.Independent

/-- Lemma 5.4, PDF p.19 (printed p.18). No density or finite-mean assumption on D₁. -/
theorem lemma_5_4 (D₁ : Measure ℝ≥0) [IsProbabilityMeasure D₁]
    (c : ℝ) (hc : 0 < c ∧ c < 1) (S : Set Option) (M : Mechanism)
    (hS : ValidMenu S) (hM : Admissible M) (hchoice : Selects S M)
    (hsingle : OnlySingleItem S) :
    Admissible (madeFree M) ∧ Selects (freeMenu S M) (madeFree M) ∧
    Structured (freeMenu S M) (freeProbability M) ∧
    lagrangian (productLaw D₁ uniformLaw) ![1, c] M ≤
      lagrangian (productLaw D₁ uniformLaw) ![1, c] (madeFree M) ∧
    (∀ i, supply (productLaw D₁ uniformLaw) (madeFree M) i ≤
      supply (productLaw D₁ uniformLaw) M i) := by sorry

end ConsumerMenuComplexity.Independent
