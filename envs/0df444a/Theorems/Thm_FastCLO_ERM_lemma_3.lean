-- Prove2me | Theorems.Thm_FastCLO_ERM_lemma_3
-- name    : FastCLO.ERM.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:21:39.543623+00:00
-- url     : https://prove2.me/theorems/0a6cbca6-13f2-47ee-a8e6-0d18c8bced03
-- title:
--   Lemma 3 — localized expected supremum of the excess-loss process of a class of Natarajan dimension at most η
-- statement:
--   Let $\mathcal Z$ be a polytope with norm bound $B$ and extreme points $\mathcal Z^\angle$, fix an instance, and let $\pi^* : \mathbb R^p \to \mathcal Z^\angle$ be a measurable optimal policy ($\pi^*(x) \in \mathcal Z^*(x)$ for almost every $x$). Let $\Pi \subseteq [\mathbb R^p \to \mathcal Z^\angle]$ be a class of measurable policies of Natarajan dimension at most $\eta$. For $\delta > 0$ define
--
--   $$\mathcal H_\delta = \Bigl\{h(X, Y; \pi) = \tfrac1B\bigl(Y^\top\pi^*(X) - Y^\top\pi(X)\bigr) : \pi \in \Pi,\ \|h\|_{L_2(P)} \le \delta\Bigr\},$$
--
--   where $\|h\|_{L_2(P)} = \sqrt{\mathbb E_P[h^2(X, Y)]}$ under the joint law $P$ of $(X, Y)$. There is a universal constant $C_0 > 0$ such that for every $n \ge 1$ with $n \ge 20C_0^2\eta\log(|\mathcal Z^\angle|^2 + 1)\log(n + 1)/\delta^2$,
--
--   $$\mathbb E_{\mathcal D}\Bigl[\sup_{h \in \mathcal H_\delta}\bigl(\mathbb E_n(h) - \mathbb E_P(h)\bigr)\Bigr] \le (1 + \sqrt2)\,C_0\sqrt{\frac{5\eta\log(|\mathcal Z^\angle|^2 + 1)\log(n + 1)}{n}}\;\delta,$$
--
--   where $\mathcal D$ is an i.i.d. sample of size $n$ and $\mathbb E_n$ its empirical mean.
--
--   The lemma bounds the mean of the localized empirical process that appears in the peeling argument for ERM; its rate is what produces the exponent $\frac{1+\alpha}{2+\alpha}$.
--
--   **Formalization Note** $C_0$ is chosen before every other quantity. The supremum over the (generally uncountable) class is assumed to be a measurable function of the data, so that its expectation is a genuine integral; the paper argues separability instead. An empty $\mathcal H_\delta$ gives supremum $0$.
-- source:
--   Hu, Kallus, Mao, Fast Rates for Contextual Linear Optimization, arXiv:2011.03030v3, Lemma 3, A.4.2, p. 24

import Mathlib
import Definitions.Def_FastCLO_ERM_ERM
import Definitions.Def_FastCLO_ERM_NatShatters
open MeasureTheory ProbabilityTheory
open scoped InnerProductSpace

namespace FastCLO.ERM

/-- **Lemma 3** (Hu, Kallus, Mao, *Fast Rates for Contextual Linear Optimization*,
arXiv:2011.03030v3, A.4.2, p. 24). Suppose the policy class `Π ⊆ [ℝ^p → Z∠]` has Natarajan
dimension at most `η`, and let
`H_δ = {h(X, Y; π) = (1/B)(Yᵀπ*(X) − Yᵀπ(X)) : π ∈ Π, ‖h‖_{L₂(P)} ≤ δ}`.
There is a universal constant `C₀` such that for any `n ≥ 20 C₀² η log(|Z∠|² + 1) log(n + 1)/δ²`,
`E_D[sup_{h ∈ H_δ}(E_n(h) − E_P(h))] ≤ (1 + √2) C₀ √(5η log(|Z∠|² + 1) log(n + 1)/n) δ`.

Formalization Note: `C₀` (taken positive, as the page's `C₀ = 90 ∫…` is) is chosen before every
other quantity. The policy class is `PC`; its members and `π*` are measurable policies, and `π*`
is optimal at almost every `x`. The supremum over the uncountable class is assumed measurable as a
function of the data (the page argues separability instead); without it a non-measurable
supremum would integrate to `0`. If `H_δ` is empty the supremum is `0`. `δ > 0` and `n ≥ 1` are
implicit on the page (it divides by both). The condition on `n` is stated literally (`n` occurs on
both sides). -/
theorem lemma_3 :
    ∃ C0 : ℝ, 0 < C0 ∧ ∀ (p d : ℕ) (P : Polytope d) (I : Instance p d)
      (PC : Set (Vec p → Vec d)) (η : ℕ) (πs : Vec p → Vec d) (n : ℕ) (δ : ℝ),
      (∀ π ∈ PC, IsPolicy P π ∧ Measurable π) →
      ¬ NatShatters PC (η + 1) →
      IsPolicy P πs → Measurable πs → (∀ᵐ x ∂I.μ, πs x ∈ Zstar P I x) →
      0 < δ → 1 ≤ n →
      20 * C0 ^ 2 * (η : ℝ) * Real.log ((P.ext.ncard : ℝ) ^ 2 + 1) * Real.log ((n : ℝ) + 1)
          / δ ^ 2 ≤ (n : ℝ) →
      let hπ : (Vec p → Vec d) → Vec p × Vec d → ℝ := fun π q =>
        (1 / P.B) * (⟪q.2, πs q.1⟫_ℝ - ⟪q.2, π q.1⟫_ℝ)
      let supDev : (Fin n → Vec p × Vec d) → ℝ := fun D =>
        ⨆ π : {π : Vec p → Vec d // π ∈ PC ∧ Real.sqrt (∫ q, hπ π q ^ 2 ∂I.joint) ≤ δ},
          ((1 / (n : ℝ)) * ∑ j, hπ π.1 (D j) - ∫ q, hπ π.1 q ∂I.joint)
      Measurable supDev →
      ∫ D, supDev D ∂(I.sample n) ≤
        (1 + Real.sqrt 2) * C0 *
          Real.sqrt (5 * (η : ℝ) * Real.log ((P.ext.ncard : ℝ) ^ 2 + 1) * Real.log ((n : ℝ) + 1)
            / n) * δ := by sorry

end FastCLO.ERM
