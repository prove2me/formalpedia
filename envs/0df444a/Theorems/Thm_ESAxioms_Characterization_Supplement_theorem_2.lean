-- Prove2me | Theorems.Thm_ESAxioms_Characterization_Supplement_theorem_2
-- name    : ESAxioms.Characterization.Supplement.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:28:52.335711+00:00
-- url     : https://prove2.me/theorems/4b1e6f4c-e401-490f-af37-99a3e3e9b6bf
-- title:
--   Theorem 2, p. 10 — on Lq, 0 ≤ q < 1, a functional satisfies Axioms M, LI, P and NRC iff it is identically zero
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space and let $q\in[0,1)$. For $q>0$, $L^q$ is the set of random variables $X$ with $\mathbb E|X|^q<\infty$, and $L^0$ is the set of all random variables. A functional $\rho:L^q\to\mathbb R$ satisfies
--
--   1. **Axiom M** if $\rho(X)\le\rho(Y)$ whenever $X\le Y$;
--   2. **Axiom LI** if $\rho(X)=\rho(Y)$ whenever $X$ and $Y$ have the same distribution;
--   3. **Axiom P** if $\rho(X)\le\lim_k\rho(\xi_k)$ whenever $\xi_k\to X$ pointwise and the limit exists;
--   4. **Axiom NRC** if there is an event $A$ with $0<\mathbb P(A)<1$ such that $\rho(X+Y)=\rho(X)+\rho(Y)$ for all $X,Y\in L^q$ sharing the tail event $A$.
--
--   **Theorem 2.** $\rho$ satisfies Axioms M, LI, P and NRC if and only if
--   $$\rho(X)=0\qquad\text{for every }X\in L^q .$$
--
--   Together with Theorem 1, which characterizes the expected shortfall $\mathrm{ES}_p$ on $L^1$ under the same four axioms, this shows that $L^1$ is the largest natural domain: on any space $L^q$ with $q<1$ only the zero functional satisfies the axioms. No normalization $\rho(1)=1$ is assumed.
--
--   **Formalization Note** Random variables are functions $\Omega\to\mathbb R$; $L^q$ is the published `Lq P q` (measurable $X$ with `MemLp X q P`, $q\in\mathbb R_{\ge0}^\infty$, $q<1$), so $q=0$ gives every measurable $X$. Axiom M uses the sure order and Axiom P pointwise convergence at every scenario, the published base conventions. The stress event of Axiom NRC has $0<\mathbb P(A)<1$, as in the base mission.
--
--   Differences from the source:
--   - encoding: standing assumption of §1.2, p. 5: the probability space is atomless → explicit hypothesis hP : IsAtomless P; reason: the paper fixes an atomless space once for the whole paper; Lean has no standing assumptions
--   - encoding: L^q, q ∈ [0, 1): random variables with finite q-th moment, L⁰ all random variables → Lq P q = {X | Measurable X ∧ MemLp X q P} with q : ℝ≥0∞, q < 1; reason: published base domain; MemLp X 0 P is a.e. strong measurability, so q = 0 gives all measurable X
--   - encoding: Axioms M and P (p. 6) → sure order X ω ≤ Y ω at every ω in M, pointwise convergence at every ω in P (published AxiomM, AxiomP); reason: the paper's own weakest forms (Remark 1, p. 7), reused unchanged from the base mission
--   - reading: Axiom NRC (p. 8): there exists an event A such that ρ(X + Y) = ρ(X) + ρ(Y) for all X, Y sharing the tail event A → published AxiomNRC: the stress event also satisfies 0 < ℙ(A) < 1; reason: a tail event has 0 < ℙ(A) < 1, so the literal reading is satisfied vacuously by A = ∅; then VaRₚ (which satisfies M, LI and P) would satisfy all four axioms and be non-zero on Lq, contradicting the theorem; the paper's p = 1 − ℙ(A) ∈ (0, 1) shows the intended reading
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 10, Theorem 2 (proof pp. 22–23); axioms p. 6 and p. 8; L^q p. 5

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization.Supplement

theorem theorem_2 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (q : ENNReal) (hq : q < 1)
    (ρ : (Ω → ℝ) → ℝ) :
    (AxiomM (Lq P q) ρ ∧ AxiomLI P (Lq P q) ρ ∧ AxiomP (Lq P q) ρ ∧ AxiomNRC P (Lq P q) ρ) ↔
      ∀ X ∈ Lq P q, ρ X = 0 := by sorry

end ESAxioms.Characterization.Supplement
