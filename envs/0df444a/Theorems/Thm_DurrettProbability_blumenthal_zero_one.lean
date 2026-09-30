-- Prove2me | Theorems.Thm_DurrettProbability_blumenthal_zero_one
-- name    : DurrettProbability.blumenthal_zero_one
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T18:28:20.73824+00:00
-- url     : https://prove2.me/theorems/eed4be13-03ef-41a3-94c9-d8fee01a6567
-- title:
--   Theorem 7.2.3 — Blumenthal's 0-1 law
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space and $B$ a Brownian motion on it whose
--   coordinate maps $B_t$ are measurable. Let
--   $$\mathcal F^{+}_{0}\ =\ \bigcap_{t>0}\ \sigma(B_s:s\le t)$$
--   be the germ $\sigma$-field at time zero. Then for every $A\in\mathcal F^{+}_{0}$,
--   $$\mathbb P(A)=0\qquad\text{or}\qquad \mathbb P(A)=1 .$$
--
--   The germ $\sigma$-field is strictly larger than $\sigma(B_0)$ — it contains, for instance, the
--   events on which $\limsup_{t\downarrow0}B_t/f(t)$ exceeds a level, for any positive $f$ — so this
--   is a genuine zero-one law and not a statement about a trivial $\sigma$-field. What it says is
--   that the infinitesimal peek at the future which $\mathcal F^{+}_{0}$ allows carries no
--   probabilistic information.
--
--   **Formalization Note** The process is a Brownian motion in Mathlib's sense: its
--   finite-dimensional laws are the Brownian ones and almost every path is continuous. In
--   particular $B_0=0$ almost surely, so this is Durrett's statement under $\mathbb P_0$; the family
--   $\{\mathbb P_x\}_{x\in\mathbb R^d}$ has no analogue on an abstract probability space, and the
--   quantifier over $x$ in the book is therefore absent.
--
--   Measurability of every $B_t$ is assumed explicitly. A Brownian motion in the library sense gives
--   only almost-everywhere measurability, and it is measurability that places the past
--   $\sigma$-fields — and hence the germ field — below the ambient $\sigma$-field, which is what
--   makes $\mathbb P(A)$ the measure of $A$ rather than an outer measure. Every standard
--   construction of Brownian motion satisfies it.
--
--   The past $\sigma$-field is the supremum of the pullbacks of the Borel field along $B_s$ for
--   $s\le t$, and the germ field the infimum of those over $t>0$; both are taken in the lattice of
--   $\sigma$-algebras on $\Omega$.
--
--   Existence of a Brownian motion is not asserted, here or anywhere in this mission: it is a
--   hypothesis. The statement is therefore not vacuous in the mathematical sense — Brownian motion
--   exists, by Durrett's Theorem 7.1.1 — although the library does not yet construct one.
-- source:
--   Durrett, Probability: Theory and Examples, Version 5 (11 January 2019), p. 362 (PDF p. 370), Theorem 7.2.3: 'Blumenthal's 0-1 law. If A in F^+_0 then for all x in R^d, P_x(A) in {0, 1}.' Proof: 'Using A in F^+_0, Theorem 7.2.2, and F^o_0 = sigma(B_0) is trivial under P_x gives 1_A = E_x(1_A|F^+_0) = E_x(1_A|F^o_0) = P_x(A), P_x a.s. This shows that the indicator function 1_A is a.s. equal to the number P_x(A), and the result follows.' The germ field is defined on p. 360 (PDF p. 368): 'F^o_s = sigma(B_r : r <= s) ... it is convenient to replace F^o_s by F^+_s = intersection over t > s of F^o_t.' sha256 aeac36cbf5e44c53d69fa60a2d29a393e2d0e8c955ee103bd845d925fd910886

import Mathlib
import Definitions.Def_DurrettProbability_Brownian

open Filter MeasureTheory ProbabilityTheory
open scoped NNReal Topology

namespace DurrettProbability

theorem blumenthal_zero_one {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {B : ℝ≥0 → Ω → ℝ} (hB : IsBrownianReal B P)
    (hBm : ∀ t, Measurable (B t)) {A : Set Ω} (hA : MeasurableSet[germSigma B] A) :
    P A = 0 ∨ P A = 1 := by sorry

end DurrettProbability
