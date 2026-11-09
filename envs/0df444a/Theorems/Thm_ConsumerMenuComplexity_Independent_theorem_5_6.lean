-- Prove2me | Theorems.Thm_ConsumerMenuComplexity_Independent_theorem_5_6
-- name    : ConsumerMenuComplexity.Independent.theorem_5_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T08:11:43.148614+00:00
-- url     : https://prove2.me/theorems/2424bdad-d0c5-4f4c-be99-4d6d17faffb8
-- title:
--   Theorem 5.6 — global L-optimality, rigidity, and no finite optimum
-- statement:
--   A mechanism assigns allocation probabilities $x_1(v),x_2(v)$ and payment $p(v)$ to every type $v=(v_1,v_2)\in\mathbb R_{\ge0}^2$. It is admissible when the rules are Borel measurable, $0\le x_i\le1$, $x_1+x_2\le1$, $p\ge0$, and the buyer's utility $u^M(v)=v_1x_1(v)+v_2x_2(v)-p(v)$ is nonnegative and is at least the payoff from every other report. All mechanism comparisons below range over this entire admissible class.
--
--   For a prior $D$, write $U_D(M)=\mathbb E_D[u^M]$, $a_i^D(M)=\mathbb E_D[x_i^M]$, and $L_{D,(\lambda_1,\lambda_2)}(M)=U_D(M)-\lambda_1a_1^D(M)-\lambda_2a_2^D(M)$. A menu includes the null option, has feasible nonnegative-price triples, and is equipped with an actual utility-maximizing choice at every type.
--
--   Take exactly the density (19), normalized by its actual integral, $D_2=U(0,1)$ independently, and $c=1/8$. The unnormalized density is integrable with positive integral; the normalized density is genuine and satisfies F1–F4, and both marginal laws are probability measures. The menu $M^*$ in (14) is valid with its defined maximizing selection and utility
--   $$u^{M^*}(v_1,v_2)=\max\{r(v_1),v_2\}.$$
--   It is admissible and globally maximizes $L$ over every admissible mechanism. Every global maximizer $M$ satisfies
--   $$u^M(a,0)=\frac a4+\frac{a^2}{8}\quad(0<a<2),$$
--   and has infinitely many distinct selected non-null triples on the support of the constructed prior. In particular, no mechanism with a finite such menu can maximize $L$.
--
--   The probability and construction validations are conclusions, not assumptions. No structuredness, differentiability or prescribed utility condition is imposed on global competitors.
--
--   Differences from the source:
--   - encoding: two nonnegative real item values and truthful unit-demand mechanisms with nonnegative payments → Fin 2 coordinates in the nonnegative reals, the published raw mechanism defined at every report of the full orthant (also outside support(D)), IC/IR/NPT and unit-demand feasibility at all those reports, and Borel measurable allocation/payment rules; reason: coordinates 0 and 1 represent items 1 and 2; a truthful mechanism on the support extends to the orthant by the closure of its menu, without changing it on the support; a rule measurable only for the completed prior agrees a.e. with a Borel subgradient selection having the same utility, so no objective changes; no smoothness or finite-support restriction is imposed
--   - encoding: expected utility and modified expected utility minus allocation costs → nonnegative extended utility expectation and subtraction of the finite real expected allocation cost; ordinary real expected allocations; reason: admissibility bounds allocations on a probability space; this prevents a nonintegrable utility from defaulting to zero and retains infinite-mean priors where the source allows them
--   - generalization: M* maximizes L, every maximizer has the quadratic axis utility, and no finite menu maximizes L; the construction is verified separately in Appendix B.1 → the same three claims, plus as added conclusions: integrability and positive integral of the raw density, IsDensity and F1–F4 for it, the probability laws, validity of the menu with u = max(r(v1), v2), and infinitely many selected non-null triples on the actual prior support for every maximizer; reason: each added clause is proved in the source (Appendix B.1, §5.3, proof of Theorem 5.6); dropping them gives the source theorem, and infinitude on the support implies that no finite menu maximizes L
--   - encoding: derivative identities interpreted almost everywhere by footnote 9 → F2 at each differentiability point, F3 and F4 identities Lebesgue almost everywhere, and pointwise final utility identities; reason: this preserves the source nondifferentiable competitors and the breakpoint at 2; F3 positivity remains pointwise
--   - encoding: menu (14) with appropriate tie-breaking → targetMenu is (14) plus the null option, and targetMechanism is an explicit selection (item 1 on a tie between r(v1) and v2, tangent t=v1 through v1=2); reason: §2.1 includes the null option in every menu and leaves tie-breaking to the mechanism; the null option is dominated and the ties have probability zero
-- source:
--   Goldner, Mohan and Phung, On the Menu Complexity of Consumer Utility Maximization, November 3, 2026 preprint, STOC 2027 submission #10, SHA-256 4baa3f39e319dd0a0dd217840839edadc0a463c80f799a7858fa61ddc5de9cb4, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/10.pdf, Theorem 5.6, PDF p.21 (printed p.20), proof PDF p.22; construction checks Appendix B.1 PDF p.34; §2.1 footnote 5 PDF p.8

import Mathlib
import Definitions.Def_ConsumerMenuComplexity_Independent_DensityConditions
open MeasureTheory
open scoped NNReal

namespace ConsumerMenuComplexity.Independent

/-- Theorem 5.6 (PDF p.21) and validity of its explicit construction (PDF p.34).
No normalization, integrability or optimality of the construction is assumed. -/
theorem theorem_5_6 :
    Integrable rawDensity ∧ 0 < (∫ v : ℝ, rawDensity v) ∧
    IsDensity firstDensity ∧ F1 firstDensity ∧ F2 firstDensity ∧
    F3 firstDensity (1 / 8) ∧ F4 firstDensity ∧
    IsProbabilityMeasure firstLaw ∧ IsProbabilityMeasure uniformLaw ∧
    ValidMenu targetMenu ∧ Selects targetMenu targetMechanism ∧
    (∀ v : TypeSpace, utility targetMechanism v = max (targetUtility (v 0)) (v 1)) ∧
    LOptimal constructedPrior chosenCosts targetMechanism ∧
    (∀ M : Mechanism, LOptimal constructedPrior chosenCosts M →
      (∀ a : ℝ≥0, 0 < a → a < 2 → utility M (typeAt a 0) = (a : ℝ) / 4 + (a : ℝ) ^ 2 / 8) ∧
      (nonNullOptions constructedPrior M).Infinite) ∧
    (∀ M : Mechanism, Admissible M → (nonNullOptions constructedPrior M).Finite →
      ¬ LOptimal constructedPrior chosenCosts M) := by sorry

end ConsumerMenuComplexity.Independent
