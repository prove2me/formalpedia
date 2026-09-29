-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString
-- name    : AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/5414e7e1-abb0-55ef-9d6a-1fdeac678656
-- title:
--   Continuous twisted section functions for complex conjugation on GL₂
-- statement:
--   Work in the group $G = \mathrm{GL}_2(\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R})$, with $\sigma$ the map on $G$ induced entrywise by the conjugation automorphism `Complex.conjAe` of $\mathbb{C}$ over $\mathbb{R}$ (tensored with $\mathbb{R}$), written `sigmaGL`. Let $\delta \in G$ be such that its norm string $N(\delta) = \delta \cdot \sigma(\delta)$ (the product of $\sigma^{i}(\delta)$ for $i < \operatorname{finrank}_{\mathbb{R}} \mathbb{C} = 2$) is regular semisimple in the sense that $\operatorname{tr}(N(\delta))^2 - 4\det(N(\delta))$ is a unit of $\mathbb{C} \otimes_{\mathbb{R}} \mathbb{R}$. Let $T = \{t \in G : t\,\delta\,\sigma(t)^{-1} = \delta\}$ be the twisted centralizer of $\delta$, equipped with the Borel $\sigma$-algebra of its subspace topology, let $\tau'$ be a Haar measure on $T$, and let $\varphi : G \to \mathbb{C}$ have compact support. The assertion is that there exists $W : G \to \mathbb{R}$ which is continuous and is a twisted section function for $(\delta, \tau', \varphi)$, i.e. $W(x) \ge 0$ for all $x$, $W$ is measurable for the Borel $\sigma$-algebra on $G$, $W$ has compact support, and for every $x \in G$ with $\varphi(x^{-1}\delta\,\sigma(x)) \neq 0$ one has $\int_{T} W(t x)\, d\tau'(t) = 1$.
--
--   This is the archimedean model case, for the quadratic extension $\mathbb{C}/\mathbb{R}$ and complex conjugation, of the existence of continuous section functions used to unfold twisted orbital integrals on $\mathrm{GL}_2$ at a class whose norm is regular. It is cited in the comparison of twisted orbital integrals for conjugation with ordinary orbital integrals at regular classes and at norm conjugators.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory AutomorphicForm
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.exists_isTwistedSectionFnOn_and_continuous_conjAe_of_isRegularSemisimple_normString
    (δ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ))
    (hδ : IsRegularSemisimple (normString ℝ ℂ ℝ Complex.conjAe δ))
    (τ' : @Measure (twistedCentralizer ℝ ℂ ℝ Complex.conjAe δ) (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (twistedCentralizerBorel ℝ ℂ ℝ Complex.conjAe δ) τ')
    (φ : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℂ) (hφ : HasCompactSupport φ) :
    ∃ W : GL (Fin 2) (ℂ ⊗[ℝ] ℝ) → ℝ,
      IsTwistedSectionFnOn ℝ ℂ ℝ Complex.conjAe δ τ' φ W ∧ Continuous W := by sorry
