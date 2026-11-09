-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_lemma_B_2
-- name    : ConsumerMenuComplexity.Independent.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:10:37.095195+00:00
-- url     : https://prove2.me/theorems/208c8bf5-1be1-424d-af9d-bf86ca789b32
-- title:
--   Lemma B.2 — scaling for every d and strictness for d < 1
-- statement:
--   A mechanism assigns allocation probabilities $x_1(v),x_2(v)$ and payment $p(v)$ to every type $v=(v_1,v_2)\in\mathbb R_{\ge0}^2$. It is admissible when the rules are Borel measurable, $0\le x_i\le1$, $x_1+x_2\le1$, $p\ge0$, and the buyer's utility $u^M(v)=v_1x_1(v)+v_2x_2(v)-p(v)$ is nonnegative and is at least the payoff from every other report. All mechanism comparisons below range over this entire admissible class.
--
--   For a prior $D$, write $U_D(M)=\mathbb E_D[u^M]$, $a_i^D(M)=\mathbb E_D[x_i^M]$, and $L_{D,(\lambda_1,\lambda_2)}(M)=U_D(M)-\lambda_1a_1^D(M)-\lambda_2a_2^D(M)$. A menu includes the null option, has feasible nonnegative-price triples, and is equipped with an actual utility-maximizing choice at every type.
--
--   Use the constructed product prior $D_1\times U(0,1)$ of equation (19), the full menu $M^*$ of equation (14), and costs $(1,1/8)$. Let $M$ be any admissible selection from any valid structured menu whose item-2 option is $(0,d,0)$, where $0\le d\le1$. Then
--   $$L(M)\le dL(M^*),\qquad d<1\ \Longrightarrow\ L(M)<L(M^*).$$
--   Both conclusions include $d=0$. The item-1 options and their selections remain arbitrary throughout the quantified structured class. This rules out any optimal structured mechanism with a smaller fallback allocation probability.
--
--   Differences from the source:
--   - encoding: two nonnegative real item values and truthful unit-demand mechanisms with nonnegative payments → Fin 2 coordinates in the nonnegative reals, the published raw mechanism defined at every report of the full orthant (also outside support(D)), IC/IR/NPT and unit-demand feasibility at all those reports, and Borel measurable allocation/payment rules; reason: coordinates 0 and 1 represent items 1 and 2; a truthful mechanism on the support extends to the orthant by the closure of its menu, without changing it on the support; a rule measurable only for the completed prior agrees a.e. with a Borel subgradient selection having the same utility, so no objective changes; no smoothness or finite-support restriction is imposed
--   - encoding: expected utility and modified expected utility minus allocation costs → nonnegative extended utility expectation and subtraction of the finite real expected allocation cost; ordinary real expected allocations; reason: admissibility bounds allocations on a probability space; this prevents a nonintegrable utility from defaulting to zero and retains infinite-mean priors where the source allows them
--   - encoding: structured menus satisfying S1 and S2 with free probability d → explicit valid menu, admissible maximizing selection and the Structured predicate including 0 ≤ d ≤ 1; reason: this includes the null-lottery case d=0 and counts arbitrary item-1 lotteries without a division by d
--   - encoding: menu (14) with appropriate tie-breaking → targetMenu is (14) plus the null option, and targetMechanism is an explicit selection (item 1 on a tie between r(v1) and v2, tangent t=v1 through v1=2); reason: §2.1 includes the null option in every menu and leaves tie-breaking to the mechanism; the null option is dominated and the ties have probability zero
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Lemma B.2, PDF p.34 (printed p.33); Appendix B.2 proof, PDF pp.35–36

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Construction

namespace ConsumerMenuComplexity.Independent

/-- Lemma B.2, PDF p.34 (printed p.33), including d=0 and strictness. -/
theorem lemma_B_2 (d : ℝ) (S : Set Option) (M : Mechanism)
    (hS : ValidMenu S) (hM : Admissible M) (hchoice : Selects S M)
    (hstructured : Structured S d) :
    lagrangian constructedPrior chosenCosts M ≤
      (d : EReal) * lagrangian constructedPrior chosenCosts targetMechanism ∧
    (d < 1 → lagrangian constructedPrior chosenCosts M <
      lagrangian constructedPrior chosenCosts targetMechanism) := by sorry

end ConsumerMenuComplexity.Independent
