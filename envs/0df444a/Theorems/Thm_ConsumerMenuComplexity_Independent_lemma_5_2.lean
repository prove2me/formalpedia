-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_lemma_5_2
-- name    : ConsumerMenuComplexity.Independent.lemma_5_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:15:59.484307+00:00
-- url     : https://prove2.me/theorems/06332602-2a7c-46d6-986f-1299762b3f2c
-- title:
--   Lemma 5.2 — projection improves L and each supply
-- statement:
--   A mechanism assigns allocation probabilities $x_1(v),x_2(v)$ and payment $p(v)$ to every type $v=(v_1,v_2)\in\mathbb R_{\ge0}^2$. It is admissible when the rules are Borel measurable, $0\le x_i\le1$, $x_1+x_2\le1$, $p\ge0$, and the buyer's utility $u^M(v)=v_1x_1(v)+v_2x_2(v)-p(v)$ is nonnegative and is at least the payoff from every other report. All mechanism comparisons below range over this entire admissible class.
--
--   For a prior $D$, write $U_D(M)=\mathbb E_D[u^M]$, $a_i^D(M)=\mathbb E_D[x_i^M]$, and $L_{D,(\lambda_1,\lambda_2)}(M)=U_D(M)-\lambda_1a_1^D(M)-\lambda_2a_2^D(M)$. A menu includes the null option, has feasible nonnegative-price triples, and is equipped with an actual utility-maximizing choice at every type.
--
--   Let $D_1$ have a genuine density $f$ satisfying F1 and F2, and let $D_2=U(0,1)$ independently. F1 includes continuity, piecewise smoothness, the two zero boundary limits of $vf(v)$ and finite mean. F2 states $f+f'\le0$ wherever differentiable. Fix $0<c<1$ and costs $(1,c)$. For every admissible mechanism $M$, its same-price projection $M^{\rm proj}$ is admissible, selects from the projected original menu, uses only single-item lotteries, and satisfies
--   $$L_{D,(1,c)}(M)\le L_{D,(1,c)}(M^{\rm proj}),\qquad a_i^D(M^{\rm proj})\le a_i^D(M)\quad(i=1,2).$$
--   Thus it supplies the source's replacement without an objective loss or an increase in either item's expected allocation. F1 permits an unbounded density at zero.
--
--   Differences from the source:
--   - encoding: two nonnegative real item values and truthful unit-demand mechanisms with nonnegative payments → Fin 2 coordinates in the nonnegative reals, the published raw mechanism defined at every report of the full orthant (also outside support(D)), IC/IR/NPT and unit-demand feasibility at all those reports, and Borel measurable allocation/payment rules; reason: coordinates 0 and 1 represent items 1 and 2; a truthful mechanism on the support extends to the orthant by the closure of its menu, without changing it on the support; a rule measurable only for the completed prior agrees a.e. with a Borel subgradient selection having the same utility, so no objective changes; no smoothness or finite-support restriction is imposed
--   - encoding: expected utility and modified expected utility minus allocation costs → nonnegative extended utility expectation and subtraction of the finite real expected allocation cost; ordinary real expected allocations; reason: admissibility bounds allocations on a probability space; this prevents a nonintegrable utility from defaulting to zero and retains infinite-mean priors where the source allows them
--   - generalization: continuous piecewise smooth density on the positive half-line → continuous density locally piecewise C¹, with finitely many breakpoints on each compact subinterval of the positive half-line; reason: piecewise smooth densities satisfy this condition; only the first derivative is used, and no smoothness or boundedness at zero is imposed
--   - generalization: there exists a single-item replacement → the defined projection is admissible and gives that replacement; reason: the source proof constructs this same-price projection, so the Lean conclusion names the witness of the source existential and implies it; its selection is explicit rather than assumed
--   - encoding: density f1 of D1 on the positive half-line → a measurable f : ℝ → ℝ that is zero on the nonpositive half-line, with D1 the pushforward to the nonnegative reals of Lebesgue measure with density f; reason: values at a single point and the extension by zero change no distribution
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Lemma 5.2, PDF p.17 (printed p.16); construction and supply computation PDF pp.17–18

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Transforms
import Definitions.Def_ConsumerMenuComplexity_Independent_DensityConditions

namespace ConsumerMenuComplexity.Independent

/-- Lemma 5.2, PDF p.17 (printed p.16), with §3 costs and all supply clauses. -/
theorem lemma_5_2 (f : ℝ → ℝ) (hf : IsDensity f) (hF1 : F1 f) (hF2 : F2 f)
    (c : ℝ) (hc : 0 < c ∧ c < 1) (M : Mechanism) (hM : Admissible M) :
    Admissible (projected M) ∧
    Selects (projectMenu (offered M)) (projected M) ∧
    OnlySingleItem (projectMenu (offered M)) ∧
    lagrangian (productLaw (densityLaw f) uniformLaw) ![1, c] M ≤
      lagrangian (productLaw (densityLaw f) uniformLaw) ![1, c] (projected M) ∧
    (∀ i, supply (productLaw (densityLaw f) uniformLaw) (projected M) i ≤
      supply (productLaw (densityLaw f) uniformLaw) M i) := by sorry

end ConsumerMenuComplexity.Independent
