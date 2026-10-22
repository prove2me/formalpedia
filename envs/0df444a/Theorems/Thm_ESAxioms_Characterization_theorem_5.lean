-- Prove2me | Theorems.Thm_ESAxioms_Characterization_theorem_5
-- name    : ESAxioms.Characterization.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:40.076137+00:00
-- url     : https://prove2.me/theorems/d38d5bca-2242-4752-9c9a-49e93a85aa5a
-- title:
--   Theorem 5, p. 15 — p-concentration ⇔ maximizing the ESₚ aggregation ⇔ ESₚ additivity
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be an atomless probability space, $p\in(0,1)$, and let $(X_1,\dots,X_n)$ be a random vector with all components in $L^1$. The following are equivalent:
--
--   1. $(X_1,\dots,X_n)$ is $p$-concentrated;
--   2. $(X_1,\dots,X_n)$ maximizes the $\mathrm{ES}_p$ aggregation;
--   3. $$\mathrm{ES}_p\Big(\sum_{i=1}^n X_i\Big)=\sum_{i=1}^n \mathrm{ES}_p(X_i).$$
--
--   In particular $\mathrm{ES}_p$ is additive exactly on $p$-concentrated portfolios, which is what makes it satisfy Axiom NRC.
--
--   **Formalization Note** The vector is `Xs : Fin n → Ω → ℝ`; no lower bound on $n$ is imposed (for $n=0$ all three statements hold). In (2) the competitors $X_i'$ range over measurable random variables with $X_i'\overset{d}{=}X_i$.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 15, Theorem 5 (with Definition 4)

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem theorem_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (hP : TailRiskSharing.VaRConv.IsAtomless P) (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1)
    {n : ℕ} (Xs : Fin n → Ω → ℝ) (hXs : ∀ i, Xs i ∈ L1 P) :
    List.TFAE [IsPConcentrated P p Xs, MaximizesESAggregation P p Xs,
      ES P p (fun ω => ∑ i, Xs i ω) = ∑ i, ES P p (Xs i)] := by sorry

end ESAxioms.Characterization
