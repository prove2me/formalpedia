-- Prove2me | Theorems.Thm_ESAxioms_Characterization_Supplement_theorem_6
-- name    : ESAxioms.Characterization.Supplement.theorem_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:34:18.815279+00:00
-- url     : https://prove2.me/theorems/e303502e-11dd-4461-8474-0d82110b40ef
-- title:
--   Theorem 6, pp. 15–16 — for p-concentrated losses VaRₚ(∑Xᵢ) ⩽ ∑VaRₚ(Xᵢ) ⩽ ∑VaR⁺ₚ(Xᵢ) ⩽ VaR⁺ₚ(∑Xᵢ), each possibly strict; VaRₚ is not p-additive
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $p\in(0,1)$. For a random variable $X$, the left and right $p$-quantiles are
--   $$\mathrm{VaR}_p(X)=\inf\{x\in\mathbb R:\mathbb P(X\le x)\ge p\},\qquad \mathrm{VaR}^+_p(X)=\inf\{x\in\mathbb R:\mathbb P(X\le x)>p\}.$$
--
--   **Theorem 6.** Let $(X_1,\dots,X_n)$ be any $p$-concentrated random vector. Then
--   $$\mathrm{VaR}_p\Big(\sum_{i=1}^n X_i\Big)\le\sum_{i=1}^n\mathrm{VaR}_p(X_i)\le\sum_{i=1}^n\mathrm{VaR}^+_p(X_i)\le\mathrm{VaR}^+_p\Big(\sum_{i=1}^n X_i\Big).\tag{2}$$
--   Each inequality in (2) can be strict: for each of the three inequalities there is a $p$-concentrated random vector, with integrable components, for which that inequality is strict. Consequently $\mathrm{VaR}_p$ is not $p$-additive: there are integrable $X,Y$ sharing a tail event of probability $1-p$ with $\mathrm{VaR}_p(X+Y)\ne\mathrm{VaR}_p(X)+\mathrm{VaR}_p(Y)$.
--
--   On $p$-concentrated vectors the left quantile is subadditive and the right quantile superadditive, in contrast with $\mathrm{ES}_p$, which is additive exactly on $p$-concentrated vectors (Theorem 5). This is why $\mathrm{VaR}_p$ fails Axiom NRC and is excluded by the characterization of Theorem 1.
--
--   **Formalization Note** $\mathrm{VaR}_p$ is the base mission's `VaR P p` and $\mathrm{VaR}^+_p$ the published right quantile `VaRR P (1 - p)`. The inequalities are stated for measurable components of any dimension $n$, with no integrability or continuity assumption. Atomlessness, the paper's standing assumption, is needed only for the existence of the strictness witnesses. The strictness witnesses and the failure of $p$-additivity are stated for integrable random variables, which is stronger than the paper's sentence.
--
--   Differences from the source:
--   - encoding: standing assumption of §1.2, p. 5: the probability space is atomless → explicit hypothesis hP : IsAtomless P; reason: the paper fixes an atomless space once for the whole paper; Lean has no standing assumptions
--   - encoding: random variables X : Ω → ℝ → functions Ω → ℝ with an explicit Measurable hypothesis; reason: Lean convention; the base mission represents random variables as functions, not a.e. classes
--   - encoding: VaR⁺ₚ(X) = inf{x ∈ ℝ : ℙ(X ⩽ x) > p} (p. 15) → published VaRR P (1 - p) X = sInf {x | 1 - (1 - p) < distFn P X x}; reason: the published right quantile in the small-α convention with α = 1 − p; same value
--   - reading: each inequality in (2) is generally not an equality → for the fixed p, three separate existence statements: a p-concentrated vector (of some dimension n) for which the first, the second, respectively the third inequality is strict; reason: 'generally not an equality' means that equality can fail; the proof (pp. 34–35) exhibits a different vector for each inequality
--   - generalization: VaRₚ (on L⁰) is not p-additive; counterexample vectors are arbitrary random vectors → the witness vectors are integrable (components in L¹) and ¬ IsPAdditive P p (L1 P) (VaR P p); reason: an integrable witness is a random vector, and p-additivity on L⁰ implies p-additivity on L¹, so the Lean statement implies the source's
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), pp. 15–16, Theorem 6 and (2) (proof pp. 34–35); VaR⁺ₚ p. 15

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory TailRiskSharing.VaRConv

namespace ESAxioms.Characterization.Supplement

theorem theorem_6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) :
    (∀ {n : ℕ} (Xs : Fin n → Ω → ℝ), (∀ i, Measurable (Xs i)) → IsPConcentrated P p Xs →
      VaR P p (fun ω => ∑ i, Xs i ω) ≤ ∑ i, VaR P p (Xs i) ∧
      ∑ i, VaR P p (Xs i) ≤ ∑ i, VaRR P (1 - p) (Xs i) ∧
      ∑ i, VaRR P (1 - p) (Xs i) ≤ VaRR P (1 - p) (fun ω => ∑ i, Xs i ω)) ∧
    (∃ (n : ℕ) (Xs : Fin n → Ω → ℝ), (∀ i, Xs i ∈ L1 P) ∧ IsPConcentrated P p Xs ∧
      VaR P p (fun ω => ∑ i, Xs i ω) < ∑ i, VaR P p (Xs i)) ∧
    (∃ (n : ℕ) (Xs : Fin n → Ω → ℝ), (∀ i, Xs i ∈ L1 P) ∧ IsPConcentrated P p Xs ∧
      ∑ i, VaR P p (Xs i) < ∑ i, VaRR P (1 - p) (Xs i)) ∧
    (∃ (n : ℕ) (Xs : Fin n → Ω → ℝ), (∀ i, Xs i ∈ L1 P) ∧ IsPConcentrated P p Xs ∧
      ∑ i, VaRR P (1 - p) (Xs i) < VaRR P (1 - p) (fun ω => ∑ i, Xs i ω)) ∧
    ¬ IsPAdditive P p (L1 P) (VaR P p) := by sorry

end ESAxioms.Characterization.Supplement
