-- Prove2me | Theorems.Thm_EllipsoidFitting_lemma_2_17
-- name    : EllipsoidFitting.lemma_2_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T10:44:10.195262+00:00
-- url     : https://prove2.me/theorems/62efcd67-085e-4616-b0bc-fbaec1d1fbec
-- title:
--   Lemma 2.17 — $\operatorname{spec}(A)\subseteq[(1-\sqrt\gamma)^2,(1+\sqrt\gamma)^2]\pm o_d(1)$
-- statement:
--   Fix $0<a\le b<1$ and a sequence $m=m(d)$ with $a\le\gamma_d:=2m(d)/d^2\le b$ for all large $d$, and let $v_1,\dots,v_{m(d)}\sim N(0,I_d/d)$ be independent. For every $\varepsilon>0$, with probability tending to $1$,
--   $$
--   \bigl((1-\sqrt{\gamma_d})^2-\varepsilon\bigr)\|x\|^2\le x^\top Ax\le\bigl((1+\sqrt{\gamma_d})^2+\varepsilon\bigr)\|x\|^2\qquad\text{for all }x\in\mathbb R^{m(d)},
--   $$
--   that is, every eigenvalue of the symmetric matrix $A$ lies in $[(1-\sqrt{\gamma_d})^2,(1+\sqrt{\gamma_d})^2]\pm\varepsilon$.
--
--   This is the Marchenko–Pastur edge of $A$; it validates the polynomial expansion $A^{-1}=\frac1{1-\gamma}\sum_t(-1)^tq_t(A)$.
--
--   **Formalization Note** Eigenvalue containment is written with Rayleigh quotients (equivalent for symmetric $A$).
--
--   Differences from the source:
--   - reading: the range of m is not stated → every m(d) with a ≤ 2m(d)/d² ≤ b for all large d, for fixed 0 < a ≤ b < 1; reason: the paper's standing regime for these estimates: γ in a fixed compact subinterval of (0,1) (Lemma B.3, p.108; Lemma 5.11, p.65); Definitions 2.14/4.1 fix 0 < γ < 1
--   - reading: with high probability, … ± o_d(1) → for every ε > 0 the probability that the bounds fail tends to 0; reason: the paper's convention (Notation, p.5)
--   - encoding: spec(A) ⊆ [λ₋, λ₊] ± ε → λ₋‖x‖² − ε‖x‖² ≤ xᵀAx ≤ λ₊‖x‖² + ε‖x‖² for all x; reason: A is symmetric, so this is equivalent to all eigenvalues lying in the interval
--   - encoding: probability of an event → the measure of the complementary (bad) set under the product law, tending to 0; reason: outer measure needs no measurability proof; for measurable events it is the same statement
-- source:
--   de la Cerda, Potechin, Tulsiani, Xu, Sharp Phase Transition for Ellipsoid Fitting, arXiv:2608.12415 (version of Nov 3, 2026, sha256 e4268312ca36b47de9467896061e7747d1efb1efe9677b7f14bd1b0647e093bc), Lemma 2.17, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_EllipsoidFitting_matA
import Definitions.Def_EllipsoidFitting_pointLaw

set_option autoImplicit false

namespace EllipsoidFitting

open Matrix MeasureTheory Filter Topology

/-- **Lemma 2.17 (spectral radius of `A`).** de la Cerda, Potechin, Tulsiani, Xu, *Sharp Phase
Transition for Ellipsoid Fitting*, arXiv:2608.12415 (version of Nov 3, 2026), Lemma 2.17, p.23:
"With high probability, spec(A) ⊆ [(1 − √γ)², (1 + √γ)²] ± od(1), where γ = 2m/d²."

Fix `0 < a ≤ b < 1` and a sequence `m(d)` with `a ≤ γ_d := 2m(d)/d² ≤ b` for all large `d`. For
every `ε > 0`, the probability that some Rayleigh quotient `xᵀAx / ‖x‖²` of `A` lies outside
`[(1 − √γ_d)² − ε, (1 + √γ_d)² + ε]` tends to `0`.

**Formalization Note** `A` is symmetric, so "spec(A) ⊆ [λ₋, λ₊]" is stated as
`λ₋ ‖x‖² ≤ xᵀ A x ≤ λ₊ ‖x‖²` for every `x ∈ ℝ^m` (equivalent to all eigenvalues lying in
`[λ₋, λ₊]`). The regime of `γ` is the paper's standing hypothesis for these estimates (Lemma B.3,
p.108; Lemma 5.11, p.65); for `γ > 1` the claim fails. "With high probability": the probability of
the complement tends to `0`; "± o_d(1)": every fixed `ε > 0`. -/
theorem lemma_2_17 (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) (hb : b < 1) (m : ℕ → ℕ)
    (hm : ∀ᶠ d in atTop, a ≤ gammaRatio d (m d) ∧ gammaRatio d (m d) ≤ b)
    (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun d => pointLaw d (m d)
      {v | ¬ ∀ x : Fin (m d) → ℝ,
          ((1 - Real.sqrt (gammaRatio d (m d))) ^ 2 - ε) * (x ⬝ᵥ x) ≤ x ⬝ᵥ (matA v *ᵥ x) ∧
          x ⬝ᵥ (matA v *ᵥ x) ≤ ((1 + Real.sqrt (gammaRatio d (m d))) ^ 2 + ε) * (x ⬝ᵥ x)})
      atTop (𝓝 0) := by sorry

end EllipsoidFitting
