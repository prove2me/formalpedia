-- Prove2me | Theorems.Thm_ESAxioms_Characterization_Supplement_theorem_4
-- name    : ESAxioms.Characterization.Supplement.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:33:51.018506+00:00
-- url     : https://prove2.me/theorems/66fe2091-615d-4831-b2f9-4dc5bdb4ad99
-- title:
--   Theorem 4, p. 13 — a random vector is p-concentrated for all p ∈ (0, 1) iff it is comonotonic
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and $(X_1,\dots,X_n)$ a random vector. It is *comonotonic* (Definition 3) if $X_i=f_i(Z)$ a.s. for every $i$, for some random variable $Z$ and increasing functions $f_1,\dots,f_n$; it is *$p$-concentrated* if its components share a common event of probability $1-p$ on which each of them almost surely dominates its values off the event.
--
--   **Theorem 4.**
--   $$(X_1,\dots,X_n)\ \text{is } p\text{-concentrated for every } p\in(0,1)\iff(X_1,\dots,X_n)\ \text{is comonotonic.}$$
--
--   Comonotonicity is thus $p$-concentration at all levels simultaneously, so $p$-concentration at a single level is a strictly weaker dependence notion. This places the stress-event additivity of Axiom NRC between full additivity and comonotonic additivity.
--
--   **Formalization Note** Components are measurable functions $\Omega\to\mathbb R$. The comonotonicity factor $Z$ is measurable, the $f_i$ are `Monotone`, and $X_i=f_i(Z)$ holds almost surely (definition item of this mission). The left side quantifies over every $p$ in the open interval $(0,1)$.
--
--   Differences from the source:
--   - encoding: standing assumption of §1.2, p. 5: the probability space is atomless → explicit hypothesis hP : IsAtomless P; reason: the paper fixes an atomless space once for the whole paper; Lean has no standing assumptions
--   - encoding: random variables X : Ω → ℝ → functions Ω → ℝ with an explicit Measurable hypothesis; reason: Lean convention; the base mission represents random variables as functions, not a.e. classes
--   - encoding: Definition 3: a random variable Z and increasing f₁, …, fₙ with Xᵢ = fᵢ(Z) a.s. → IsComonotonic P Xs: measurable Z, Monotone fᵢ, Xs i =ᵐ[P] fᵢ ∘ Z; reason: direct transcription; definition item of this mission
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 13, Theorem 4 (proof pp. 31–32); Definition 3, p. 12

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Supplement_Setting

open MeasureTheory ProbabilityTheory

namespace ESAxioms.Characterization.Supplement

theorem theorem_4 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) {n : ℕ} (Xs : Fin n → Ω → ℝ)
    (hXs : ∀ i, Measurable (Xs i)) :
    (∀ p ∈ Set.Ioo (0 : ℝ) 1, IsPConcentrated P p Xs) ↔ IsComonotonic P Xs := by sorry

end ESAxioms.Characterization.Supplement
