-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_theorem_5_1
-- name    : ConsumerMenuComplexity.Independent.theorem_5_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:07:14.112413+00:00
-- url     : https://prove2.me/theorems/37c94469-4be0-403c-9b5d-e6f9d95d6519
-- title:
--   Theorem 5.1 — every optimum for independent values has an infinite menu
-- statement:
--   A mechanism assigns allocation probabilities $x_1(v),x_2(v)$ and payment $p(v)$ to every type $v=(v_1,v_2)\in\mathbb R_{\ge0}^2$. It is admissible when the rules are Borel measurable, $0\le x_i\le1$, $x_1+x_2\le1$, $p\ge0$, and the buyer's utility $u^M(v)=v_1x_1(v)+v_2x_2(v)-p(v)$ is nonnegative and is at least the payoff from every other report. All mechanism comparisons below range over this entire admissible class.
--
--   For a prior $D$, write $U_D(M)=\mathbb E_D[u^M]$, $a_i^D(M)=\mathbb E_D[x_i^M]$, and $L_{D,(\lambda_1,\lambda_2)}(M)=U_D(M)-\lambda_1a_1^D(M)-\lambda_2a_2^D(M)$. A menu includes the null option, has feasible nonnegative-price triples, and is equipped with an actual utility-maximizing choice at every type.
--
--   There exist probability laws $D_1,D_2$ on the nonnegative reals, with finite first moments, and valid caps $\alpha\in[0,1]^2$, for which the target mechanism $M^*$ attains the maximum expected buyer utility and every utility-maximizing admissible mechanism has infinitely many distinct non-null selected allocation-payment triples on the support of $D_1\times D_2$:
--   $$\forall M\in\operatorname{argmax}_{a_i^{D_1\times D_2}(N)\le\alpha_i}U_{D_1\times D_2}(N),\quad \bigl|\{(x_1^M(v),x_2^M(v),p^M(v)):v\in\operatorname{support}(D_1\times D_2)\}\setminus\{(0,0,0)\}\bigr|=\infty.$$
--   The witnesses are exactly the constructed density (19), the uniform second law, and the actual expected allocations of $M^*$ from (14). Their cap formulas are also asserted:
--   $$\alpha_1=\int_0^2f_1(v)r(v)\frac{1+v}{4}\,dv+\int_2^\infty f_1(v)\,dv,\qquad \alpha_2=\int_0^2f_1(v)(1-r(v))\,dv.$$
--   Here $r(v)=v/4+v^2/8$ for $0\le v\le2$, with tail $r(v)=v-1$. The existential statement includes an actual optimum, so the universal menu lower bound cannot hold only because there are no optimizers. All unstructured or mixed-lottery admissible competitors are included.
--
--   Differences from the source:
--   - encoding: two nonnegative real item values and truthful unit-demand mechanisms with nonnegative payments → Fin 2 coordinates in the nonnegative reals, the published raw mechanism defined at every report of the full orthant (also outside support(D)), IC/IR/NPT and unit-demand feasibility at all those reports, and Borel measurable allocation/payment rules; reason: coordinates 0 and 1 represent items 1 and 2; a truthful mechanism on the support extends to the orthant by the closure of its menu, without changing it on the support; a rule measurable only for the completed prior agrees a.e. with a Borel subgradient selection having the same utility, so no objective changes; no smoothness or finite-support restriction is imposed
--   - encoding: expected utility and modified expected utility minus allocation costs → nonnegative extended utility expectation and subtraction of the finite real expected allocation cost; ordinary real expected allocations; reason: admissibility bounds allocations on a probability space; this prevents a nonintegrable utility from defaulting to zero and retains infinite-mean priors where the source allows them
--   - generalization: existence of independent priors and caps, with concrete witnesses and cap computations in the proof → existential witnesses identified with those exact laws and caps; finite moments, valid caps, the attained target optimum and both cap integrals are explicit conclusions; reason: the witnesses and cap integrals are those of the source proof, so the statement implies the existential headline theorem; attainment excludes an empty class of optima; open integration endpoints have zero density mass
--   - encoding: menu (14) with appropriate tie-breaking → targetMenu is (14) plus the null option, and targetMechanism is an explicit selection (item 1 on a tie between r(v1) and v2, tangent t=v1 through v1=2); reason: §2.1 includes the null option in every menu and leaves tie-breaking to the mechanism; the null option is dominated and the ties have probability zero
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Theorem 5.1, PDF p.15 (printed p.14); its explicit witnesses and cap identities, proof PDF p.22 (printed p.21); equation (19) PDF p.34

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_Construction
open MeasureTheory
open scoped NNReal

namespace ConsumerMenuComplexity.Independent

/-- Theorem 5.1, PDF p.15 (printed p.14); explicit witnesses and caps from PDF p.22.
All admissible mechanisms compete, including mixed lotteries and nonsmooth utilities. -/
theorem theorem_5_1 :
    ∃ (D₁ D₂ : Measure ℝ≥0) (α : Fin 2 → ℝ),
      D₁ = firstLaw ∧ D₂ = uniformLaw ∧ α = targetCaps ∧
      IsProbabilityMeasure D₁ ∧ IsProbabilityMeasure D₂ ∧
      Integrable (fun v : ℝ≥0 => (v : ℝ)) D₁ ∧
      Integrable (fun v : ℝ≥0 => (v : ℝ)) D₂ ∧
      ValidCaps α ∧
      α 0 = (∫ v in Set.Ioo (0 : ℝ) 2, firstDensity v * targetUtility v * ((1 + v) / 4)) +
        (∫ v in Set.Ioi (2 : ℝ), firstDensity v) ∧
      α 1 = (∫ v in Set.Ioo (0 : ℝ) 2, firstDensity v * (1 - targetUtility v)) ∧
      UtilityOptimal (productLaw D₁ D₂) α targetMechanism ∧
      (∀ M : Mechanism, UtilityOptimal (productLaw D₁ D₂) α M →
        (nonNullOptions (productLaw D₁ D₂) M).Infinite) := by sorry

end ConsumerMenuComplexity.Independent
