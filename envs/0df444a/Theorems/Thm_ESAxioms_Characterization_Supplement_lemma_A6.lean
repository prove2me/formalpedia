-- Prove2me | Theorems.Thm_ESAxioms_Characterization_Supplement_lemma_A6
-- name    : ESAxioms.Characterization.Supplement.lemma_A6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:31:41.321738+00:00
-- url     : https://prove2.me/theorems/d52fc061-74a7-499c-a06b-e22a07c61a96
-- title:
--   Lemma A.6, p. 29 — a p-tail event of X is one of f(X) for increasing f, and conversely for strictly increasing f
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space, $p\in(0,1)$, $X$ a random variable and $f:\mathbb R\to\mathbb R$. A $p$-tail event of $X$ is an event $A$ with $\mathbb P(A)=1-p$ such that $X(\omega)\ge X(\omega')$ for almost all $\omega\in A$ and $\omega'\in A^c$.
--
--   **Lemma A.6.**
--   1. If $f$ is increasing (non-decreasing), then every $p$-tail event of $X$ is a $p$-tail event of $f(X)$.
--   2. If $f$ is strictly increasing, then conversely every $p$-tail event of $f(X)$ is a $p$-tail event of $X$.
--
--   In symbols, for increasing $f$: $\ A \text{ is a } p\text{-tail event of } X \Rightarrow A \text{ is a } p\text{-tail event of } f(X)$, with equivalence when $f$ is strictly increasing:
--   $$X(\omega)\ge X(\omega')\ \Longrightarrow\ f(X(\omega))\ge f(X(\omega')),\qquad f(X(\omega))\ge f(X(\omega'))\ \Longrightarrow\ X(\omega)\ge X(\omega')\ (f\text{ strictly increasing}).$$
--
--   The lemma lets $p$-concentration pass through increasing transformations; it gives (i)⇔(iv) of Theorem 3 and the forward direction of Theorem 4.
--
--   **Formalization Note** $f(X)$ is the function $\omega\mapsto f(X(\omega))$; increasing and strictly increasing are `Monotone f` and `StrictMono f`.
--
--   Differences from the source:
--   - encoding: random variables X : Ω → ℝ → functions Ω → ℝ with an explicit Measurable hypothesis; reason: Lean convention; the base mission represents random variables as functions, not a.e. classes
--   - encoding: increasing function f (non-strict, p. 5); strictly increasing function → Monotone f; StrictMono f; reason: the paper's convention on p. 5
--   - encoding: p implicit in 'p-tail event' (Definition 2, p ∈ (0, 1)) → explicit hypothesis p ∈ (0, 1); reason: Definition 2 defines p-tail events for p ∈ (0, 1)
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 29, Lemma A.6

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory

namespace ESAxioms.Characterization.Supplement

theorem lemma_A6 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (f : ℝ → ℝ) (X : Ω → ℝ) (hX : Measurable X)
    (A : Set Ω) :
    (Monotone f → IsPTailEvent P p X A → IsPTailEvent P p (fun ω => f (X ω)) A) ∧
      (StrictMono f → IsPTailEvent P p (fun ω => f (X ω)) A → IsPTailEvent P p X A) := by sorry

end ESAxioms.Characterization.Supplement
