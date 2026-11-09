-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_lemma_3_1
-- name    : ConsumerMenuComplexity.Independent.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:06:53.946835+00:00
-- url     : https://prove2.me/theorems/ec73e8e6-319b-4541-8f13-cd2bb14393f5
-- title:
--   Lemma 3.1 — both caps conclusions for arbitrary positive costs
-- statement:
--   A mechanism assigns allocation probabilities $x_1(v),x_2(v)$ and payment $p(v)$ to every type $v=(v_1,v_2)\in\mathbb R_{\ge0}^2$. It is admissible when the rules are Borel measurable, $0\le x_i\le1$, $x_1+x_2\le1$, $p\ge0$, and the buyer's utility $u^M(v)=v_1x_1(v)+v_2x_2(v)-p(v)$ is nonnegative and is at least the payoff from every other report. All mechanism comparisons below range over this entire admissible class.
--
--   For a prior $D$, write $U_D(M)=\mathbb E_D[u^M]$, $a_i^D(M)=\mathbb E_D[x_i^M]$, and $L_{D,(\lambda_1,\lambda_2)}(M)=U_D(M)-\lambda_1a_1^D(M)-\lambda_2a_2^D(M)$. A menu includes the null option, has feasible nonnegative-price triples, and is equipped with an actual utility-maximizing choice at every type.
--
--   Let $D$ be any probability law on the full nonnegative quadrant and let $\lambda_1,\lambda_2>0$. Suppose an admissible mechanism $M^*$ globally attains a finite maximum of $L_{D,(\lambda_1,\lambda_2)}$. Set $\alpha_i=a_i^D(M^*)$. Then these are valid caps and $M^*$ maximizes expected utility subject to them. Furthermore, every admissible utility-maximizer $M$ under those caps also maximizes the same modified Lagrangian and exhausts both caps:
--   $$M\in\operatorname{argmax}_{a_i^D(N)\le\alpha_i}U_D(N)\ \Longrightarrow\ M\in\operatorname{argmax}_N L_{D,(\lambda_1,\lambda_2)}(N),\qquad a_i^D(M)=\alpha_i\ (i=1,2).$$
--   The prior need not have bounded support or finite first moments. Finiteness is imposed only on the attained Lagrangian maximum, as in the source.
--
--   Differences from the source:
--   - encoding: two nonnegative real item values and truthful unit-demand mechanisms with nonnegative payments → Fin 2 coordinates in the nonnegative reals, the published raw mechanism defined at every report of the full orthant (also outside support(D)), IC/IR/NPT and unit-demand feasibility at all those reports, and Borel measurable allocation/payment rules; reason: coordinates 0 and 1 represent items 1 and 2; a truthful mechanism on the support extends to the orthant by the closure of its menu, without changing it on the support; a rule measurable only for the completed prior agrees a.e. with a Borel subgradient selection having the same utility, so no objective changes; no smoothness or finite-support restriction is imposed
--   - encoding: expected utility and modified expected utility minus allocation costs → nonnegative extended utility expectation and subtraction of the finite real expected allocation cost; ordinary real expected allocations; reason: admissibility bounds allocations on a probability space; this prevents a nonintegrable utility from defaulting to zero and retains infinite-mean priors where the source allows them
--   - encoding: M* attains a finite maximum of L → LOptimal together with a real-valued certificate of the attained L value; reason: this is the stated finite maximum; no moment assumption is added
--   - generalization: M* maximizes utility under the induced caps and every utility maximizer maximizes L → those two conclusions, plus validity of the induced caps and exhaustion of both caps by every utility maximizer; reason: cap validity is noted in the proof of Theorem 5.1 and cap exhaustion is the closing sentence of the proof of Lemma 3.1; dropping them gives the source lemma
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Lemma 3.1 and the concluding cap-exhaustion sentence of its proof, PDF p.9 (printed p.8)

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Mechanisms
open MeasureTheory

namespace ConsumerMenuComplexity.Independent

/-- Lemma 3.1, PDF p.9 (printed p.8), arbitrary prior and strictly positive costs. -/
theorem lemma_3_1 (μ : Measure TypeSpace) [IsProbabilityMeasure μ]
    (cost : Fin 2 → ℝ) (hcost : ∀ i, 0 < cost i) (Mstar : Mechanism)
    (hmax : LOptimal μ cost Mstar)
    (hfinite : ∃ l : ℝ, lagrangian μ cost Mstar = (l : EReal)) :
    ValidCaps (supply μ Mstar) ∧ UtilityOptimal μ (supply μ Mstar) Mstar ∧
    (∀ M : Mechanism, UtilityOptimal μ (supply μ Mstar) M →
      LOptimal μ cost M ∧ ∀ i, supply μ M i = supply μ Mstar i) := by sorry

end ConsumerMenuComplexity.Independent
