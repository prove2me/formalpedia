-- Prove2me | Theorems.Thm_ESAxioms_Characterization_Supplement_lemma_A4
-- name    : ESAxioms.Characterization.Supplement.lemma_A4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:29:52.54963+00:00
-- url     : https://prove2.me/theorems/c10fffb2-7f6b-4e4e-9d56-5576e0d79708
-- title:
--   Lemma A.4, p. 28 — A is a p-tail event of X iff A = {U > p} a.s. for a uniform U with F_X⁻¹(U) = X a.s.
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, $X$ a random variable with cdf $F_X$, and $F_X^{-1}(u)=\inf\{x\in\mathbb R:F_X(x)\ge u\}$ its left quantile function. Recall that a $p$-tail event of $X$ is an event $A$ with $\mathbb P(A)=1-p$ such that $X(\omega)\ge X(\omega')$ for almost all $\omega\in A$ and $\omega'\in A^c$.
--
--   **Lemma A.4.** An event $A$ is a $p$-tail event of $X$ if and only if there is a random variable $U$, uniformly distributed on $[0,1]$, such that
--   $$A=\{U>p\}\ \text{a.s.}\qquad\text{and}\qquad F_X^{-1}(U)=X\ \text{a.s.}$$
--
--   The lemma represents every $p$-tail event as the upper part $\{U>p\}$ of a uniform rank variable of $X$. It is the step of Theorem 3 that converts a common $p$-tail event into a copula with diagonal value $p$, and back.
--
--   **Formalization Note** $F_X^{-1}(u)$ is the base mission's left quantile `VaR P u X`; the boundary values $u\in\{0,1\}$, where it takes a default value, carry probability zero under $U$. Uniformity is measurability of $U$ together with $\mathbb P\circ U^{-1}=$ Lebesgue measure on $[0,1]$. "$A=\{U>p\}$ a.s." is equality of $A$ and $\{U>p\}$ up to a $\mathbb P$-null set.
--
--   Differences from the source:
--   - encoding: standing assumption of §1.2, p. 5: the probability space is atomless → explicit hypothesis hP : IsAtomless P; reason: the paper fixes an atomless space once for the whole paper; Lean has no standing assumptions
--   - encoding: random variables X : Ω → ℝ → functions Ω → ℝ with an explicit Measurable hypothesis; reason: Lean convention; the base mission represents random variables as functions, not a.e. classes
--   - encoding: F_X⁻¹(U), the left quantile function of X evaluated at U → VaR P (U ω) X, the published left quantile VaRL P (1 − u) X at u = U ω; reason: F_X⁻¹(u) = VaR_u(X) for u ∈ (0, 1); at U ∈ {0, 1}, where VaR takes a default value, U has probability zero, so the almost-sure equality is unaffected
--   - encoding: U uniform on [0, 1] → Measurable U ∧ P.map U = volume.restrict [0, 1]; reason: the law of U is Lebesgue measure on [0, 1]; same convention as the published Example 1
--   - encoding: an event A → explicit hypothesis MeasurableSet A; reason: an event is a member of ℱ; A = {U > p} a.s. alone would not make A measurable
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 28, Lemma A.4 (proof p. 28)

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory

namespace ESAxioms.Characterization.Supplement

theorem lemma_A4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    (X : Ω → ℝ) (hX : Measurable X) (A : Set Ω) (hA : MeasurableSet A) :
    IsPTailEvent P p X A ↔
      ∃ U : Ω → ℝ, Measurable U ∧ P.map U = volume.restrict (Set.Icc (0 : ℝ) 1) ∧
        A =ᵐ[P] {ω | p < U ω} ∧ ∀ᵐ ω ∂P, VaR P (U ω) X = X ω := by sorry

end ESAxioms.Characterization.Supplement
