-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_lemma_B_1
-- name    : ConsumerMenuComplexity.Independent.lemma_B_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:18.099138+00:00
-- url     : https://prove2.me/theorems/6b3c197b-1c25-46d1-a9d0-cc4d3eb0c4b6
-- title:
--   Lemma B.1 — structured optimality and pointwise utility rigidity
-- statement:
--   A mechanism assigns allocation probabilities $x_1(v),x_2(v)$ and payment $p(v)$ to every type $v=(v_1,v_2)\in\mathbb R_{\ge0}^2$. It is admissible when the rules are Borel measurable, $0\le x_i\le1$, $x_1+x_2\le1$, $p\ge0$, and the buyer's utility $u^M(v)=v_1x_1(v)+v_2x_2(v)-p(v)$ is nonnegative and is at least the payoff from every other report. All mechanism comparisons below range over this entire admissible class.
--
--   For a prior $D$, write $U_D(M)=\mathbb E_D[u^M]$, $a_i^D(M)=\mathbb E_D[x_i^M]$, and $L_{D,(\lambda_1,\lambda_2)}(M)=U_D(M)-\lambda_1a_1^D(M)-\lambda_2a_2^D(M)$. A menu includes the null option, has feasible nonnegative-price triples, and is equipped with an actual utility-maximizing choice at every type.
--
--   Let $D_1$ have a genuine density $f$ satisfying F1 and F2, let $D_2=U(0,1)$ independently, and fix $0<c<1$. Assume F3: $f(a)>0$ on $(0,2)$ and $(f+f')r+cf=0$ almost everywhere there; and F4: $f+f'=0$ almost everywhere above 2. Here $r(a)=a/4+a^2/8$ through 2 and $a-1$ thereafter. Then the target menu $M^*$ with its actual maximizing selection maximizes $L$ among all structured menus whose free item-2 option is $(0,1,0)$:
--   $$L_{D,(1,c)}(M)\le L_{D,(1,c)}(M^*).$$
--   Every maximizer in that entire structured class satisfies the pointwise identity
--   $$u^M(a,0)=r(a)\qquad(0<a<2).$$
--   Optimality includes validity of the target menu and admissibility of its selection. No specialization of $f$ to equation (19) is made, and the final utility identity is not weakened to an almost-everywhere conclusion.
--
--   Differences from the source:
--   - encoding: two nonnegative real item values and truthful unit-demand mechanisms with nonnegative payments → Fin 2 coordinates in the nonnegative reals, the published raw mechanism defined at every report of the full orthant (also outside support(D)), IC/IR/NPT and unit-demand feasibility at all those reports, and Borel measurable allocation/payment rules; reason: coordinates 0 and 1 represent items 1 and 2; a truthful mechanism on the support extends to the orthant by the closure of its menu, without changing it on the support; a rule measurable only for the completed prior agrees a.e. with a Borel subgradient selection having the same utility, so no objective changes; no smoothness or finite-support restriction is imposed
--   - encoding: expected utility and modified expected utility minus allocation costs → nonnegative extended utility expectation and subtraction of the finite real expected allocation cost; ordinary real expected allocations; reason: admissibility bounds allocations on a probability space; this prevents a nonintegrable utility from defaulting to zero and retains infinite-mean priors where the source allows them
--   - generalization: continuous piecewise smooth density on the positive half-line → continuous density locally piecewise C¹, with finitely many breakpoints on each compact subinterval of the positive half-line; reason: piecewise smooth densities satisfy this condition; only the first derivative is used, and no smoothness or boundedness at zero is imposed
--   - encoding: derivative identities interpreted almost everywhere by footnote 9 → F2 at each differentiability point, F3 and F4 identities Lebesgue almost everywhere, and pointwise final utility identities; reason: this preserves the source nondifferentiable competitors and the breakpoint at 2; F3 positivity remains pointwise
--   - encoding: density f1 of D1 on the positive half-line → a measurable f : ℝ → ℝ that is zero on the nonpositive half-line, with D1 the pushforward to the nonnegative reals of Lebesgue measure with density f; reason: values at a single point and the extension by zero change no distribution
--   - encoding: menu (14) with appropriate tie-breaking → targetMenu is (14) plus the null option, and targetMechanism is an explicit selection (item 1 on a tie between r(v1) and v2, tangent t=v1 through v1=2); reason: §2.1 includes the null option in every menu and leaves tie-breaking to the mechanism; the null option is dominated and the ties have probability zero
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Lemma B.1, PDF p.32 (printed p.31); §5 footnote 9, PDF p.16

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_DensityConditions
open scoped NNReal

namespace ConsumerMenuComplexity.Independent

/-- Lemma B.1, PDF p.32 (printed p.31), for every density satisfying F1–F4. -/
theorem lemma_B_1 (f : ℝ → ℝ) (hf : IsDensity f) (hF1 : F1 f) (hF2 : F2 f)
    (c : ℝ) (hc : 0 < c ∧ c < 1) (hF3 : F3 f c) (hF4 : F4 f) :
    StructuredOptimal (productLaw (densityLaw f) uniformLaw) c 1 targetMenu targetMechanism ∧
    ∀ (S : Set Option) (M : Mechanism),
      StructuredOptimal (productLaw (densityLaw f) uniformLaw) c 1 S M →
      ∀ a : ℝ≥0, 0 < a → a < 2 → utility M (typeAt a 0) = targetUtility a := by sorry

end ConsumerMenuComplexity.Independent
