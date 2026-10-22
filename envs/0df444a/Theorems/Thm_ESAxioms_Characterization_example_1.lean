-- Prove2me | Theorems.Thm_ESAxioms_Characterization_example_1
-- name    : ESAxioms.Characterization.example_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T02:34:47.288994+00:00
-- url     : https://prove2.me/theorems/be3eb2d0-860f-4019-a7c6-52a69df5858e
-- title:
--   Example 1, p. 16 — X = U1_{Aᶜ} + 1_A, Y = (1−U)1_{Aᶜ} + 1_A share a p-tail event but VaRₚ(X + Y) < VaRₚ(X) + VaRₚ(Y)
-- statement:
--   Let $p\in(0,1)$, let $U$ be uniformly distributed on $[0,1]$, and let $A$ be an event with $\mathbb P(A)=1-p$ independent of $U$. Put
--   $$X=U\mathbf 1_{A^c}+\mathbf 1_A,\qquad Y=(1-U)\mathbf 1_{A^c}+\mathbf 1_A .$$
--   Then
--
--   1. $A$ is a common $p$-tail event of $X$ and $Y$;
--   2. $\mathrm{VaR}_p(X)=\mathrm{VaR}_p(Y)=1$ and $\mathrm{VaR}_p(X+Y)=\mathrm{VaR}_p(\mathbf 1_{A^c}+2\mathbf 1_A)=1$;
--   3. hence $\mathrm{VaR}_p(X+Y)<\mathrm{VaR}_p(X)+\mathrm{VaR}_p(Y)$, and $\mathrm{VaR}_p$ is not $p$-additive on $L^1$.
--
--   The example shows that VaR fails Axiom NRC's additivity for concentrated pairs, which separates it from ES in Theorem 1.
--
--   **Formalization Note** "Uniform on $[0,1]$" is the law statement $\mathbb P\circ U^{-1}=\lambda|_{[0,1]}$ with $U$ measurable; independence is `IndepFun` of $U$ and $\mathbf 1_A$. No atomlessness is assumed.
-- source:
--   Wang & Zitikis, An Axiomatic Foundation for the Expected Shortfall, SSRN 3423042 (version of 12 March 2020), p. 16, Example 1

import Mathlib
import Definitions.Def_ESAxioms_Characterization_Setting

open MeasureTheory ProbabilityTheory Filter Topology

namespace ESAxioms.Characterization

theorem example_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (p : ℝ) (hp : p ∈ Set.Ioo (0 : ℝ) 1) (U : Ω → ℝ) (hU : Measurable U)
    (hUlaw : P.map U = volume.restrict (Set.Icc (0 : ℝ) 1))
    (A : Set Ω) (hA : MeasurableSet A) (hPA : P.real A = 1 - p)
    (hindep : IndepFun U (A.indicator (fun _ => (1 : ℝ))) P) :
    let X : Ω → ℝ := fun ω => U ω * Aᶜ.indicator (fun _ => (1 : ℝ)) ω + A.indicator (fun _ => (1 : ℝ)) ω
    let Y : Ω → ℝ := fun ω =>
      (1 - U ω) * Aᶜ.indicator (fun _ => (1 : ℝ)) ω + A.indicator (fun _ => (1 : ℝ)) ω
    IsPTailEvent P p X A ∧ IsPTailEvent P p Y A ∧
      VaR P p X = 1 ∧ VaR P p Y = 1 ∧
      VaR P p (X + Y) =
        VaR P p (fun ω => Aᶜ.indicator (fun _ => (1 : ℝ)) ω + 2 * A.indicator (fun _ => (1 : ℝ)) ω) ∧
      VaR P p (X + Y) = 1 ∧
      VaR P p (X + Y) < VaR P p X + VaR P p Y ∧
      ¬ IsPAdditive P p (L1 P) (VaR P p) := by sorry

end ESAxioms.Characterization
