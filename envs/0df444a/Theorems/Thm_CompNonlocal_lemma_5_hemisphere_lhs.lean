-- Prove2me | Theorems.Thm_CompNonlocal_lemma_5_hemisphere_lhs
-- name    : CompNonlocal.lemma_5_hemisphere_lhs
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T22:42:58.136204+00:00
-- url     : https://prove2.me/theorems/963d58d3-5546-4d6b-bd31-dc60824ae270
-- title:
--   Lemma 5, pp.27–28 — hemisphere LHS model for $\rho(5/12)$
-- statement:
--   Let $\{E_a\}$ be a rank-one qubit POVM with finitely many outcomes, written as
--   $$E_a=p_a\Big(I-\sum_{j=1}^3r_{a,j}\sigma_j\Big),\qquad p_a=\tfrac12\operatorname{Tr}E_a,\quad r_a\in S^2 .$$
--   Then $\sum_ap_a=1$ and $\sum_ap_ar_a=0$. Let $h$ be uniform on $S^2$; Bob measures $\nu(h)$; Alice samples a candidate $a$ by measuring $I/2$, outputs it if $\langle r_a,h\rangle\ge0$, and otherwise measures a fresh qubit $\nu(-h)$ and outputs its outcome. For every output $a$ the unnormalized Bob state is
--   $$\omega_a=p_a\,\nu\big(\tfrac5{12}r_a\big)=\operatorname{Tr}_A\big((E_a\otimes I)\rho(5/12)\big). \tag{11}$$
--   Hence $\rho(5/12)$ has an LHS model for every Bob POVM and every (finite-outcome) Alice qubit POVM.
--
--   The rule is the template for the local strategy of Lemma 15, where the exact direction $r_a$ is replaced by an estimate.
--
--   Differences from the source:
--   - encoding: Alice's three-step response rule and ω_a as the induced Bob state → response probability P(a | h) = Tr(E_a I/2)·1{⟨r_a, h⟩ ≥ 0} + (Σ_c Tr(E_c I/2)·1{⟨r_c, h⟩ < 0})·Tr(E_a ν(−h)) and ω_a = ∫ P(a | h) ν(h) dµ entrywise; reason: the probability of output a given h under steps 1–3
--   - reading: 'an LHS model for every Bob POVM, and for every Alice qubit POVM after rank-one refinement and coarse-graining' → HasLHSModel (werner (5/12)): one hidden ensemble, a response for every finite-outcome Alice POVM, equality (8) for every Bob effect; reason: each Bob POVM outcome is an effect; Alice's efficient measurements have finitely many outcomes
-- source:
--   Głuch, Morimae, From Computational Nonlocality to Public-Key Encryption and Commitments, manuscript (STOC 2027 submission, sha256 e245edd7…), Lemma 5, pp.27–28, Eq. (11)

import Mathlib
import Definitions.Def_CompNonlocal_HasLHSModel
import Definitions.Def_CompNonlocal_sphereMeasure
import Definitions.Def_CompNonlocal_bloch
import Definitions.Def_CompNonlocal_werner
import Definitions.Def_WildeQIT_partialTrace

set_option autoImplicit false

open MeasureTheory
open scoped Kronecker

namespace CompNonlocal

/-- **Lemma 5 (Hemisphere LHS model for ρ(5/12)).** Głuch, Morimae, *From Computational
Nonlocality to Public-Key Encryption and Commitments*, manuscript (STOC 2027 submission, sha256
e245edd7…), pp.27–28: "Let {E_a} be a rank-one qubit POVM, written as
E_a = p_a(I − Σ_{j=1}^3 r_{a,j}σ_j), p_a := (1/2) Tr(E_a), r_a ∈ S². Σ_a p_a = 1 and Σ_a p_a r_a = 0.
Let the shared random variable h be a uniform direction in S². Bob applies his honest measurement
to ν(h). Alice uses the following response: 1. Sample a candidate a ← p, independently of h, by
measuring I/2 with {E_a}. 2. If ⟨r_a, h⟩ ≥ 0, output a. 3. Otherwise, measure a fresh qubit ν(−h)
with {E_a} and output its outcome. For every output a, the associated unnormalized Bob state is
ω_a = p_a ν((5/12) r_a) = Tr_A((E_a ⊗ I)ρ(5/12)). (11) Thus this is an LHS model for every Bob POVM,
and for every Alice qubit POVM after rank-one refinement and coarse-graining."

**Formalization Note** The POVM has a finite outcome type and is given in the displayed form, with
`p_a ≥ 0` and unit `r_a` (any unit `r_a` when `p_a = 0`). Alice's response probability is
`P(a | h) = Tr(E_a I/2) · 1{⟨r_a, h⟩ ≥ 0} + (Σ_c Tr(E_c I/2) · 1{⟨r_c, h⟩ < 0}) · Tr(E_a ν(−h))` (steps
1–3), and `ω_a = ∫ P(a | h) ν(h) dµ(h)` entrywise, `µ` the normalized sphere measure.
`Tr_A` is `WildeQIT.partialTraceLeft`. The "Thus" clause is `HasLHSModel (werner (5/12))`. -/
theorem lemma_5_hemisphere_lhs {Out : Type} [Fintype Out] (E : Out → Matrix Bool Bool ℂ)
    (p : Out → ℝ) (r : Out → EuclideanSpace ℝ (Fin 3)) (hp : ∀ a, 0 ≤ p a)
    (hr : ∀ a, ‖r a‖ = 1)
    (hE : ∀ a, E a = (p a : ℂ) • (1 - ∑ j : Fin 3, ((r a j : ℝ) : ℂ) • pauli j))
    (hpovm : ∑ a, E a = 1) :
    let resp : Out → Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → ℝ := fun a h =>
      (E a * ((1 / 2 : ℂ) • 1)).trace.re *
          (if 0 ≤ inner ℝ (r a) (h : EuclideanSpace ℝ (Fin 3)) then 1 else 0) +
        (∑ c, (E c * ((1 / 2 : ℂ) • 1)).trace.re *
            (if inner ℝ (r c) (h : EuclideanSpace ℝ (Fin 3)) < 0 then 1 else 0)) *
          (E a * bloch (-(h : EuclideanSpace ℝ (Fin 3)))).trace.re
    (∀ a, p a = (E a).trace.re / 2) ∧ ∑ a, p a = 1 ∧ ∑ a, p a • r a = 0 ∧
      (∀ a,
        (Matrix.of fun i j =>
            ∫ h, ((resp a h : ℝ) : ℂ) * bloch (h : EuclideanSpace ℝ (Fin 3)) i j ∂sphereMeasure) =
          (p a : ℂ) • bloch ((5 / 12 : ℝ) • r a) ∧
        (p a : ℂ) • bloch ((5 / 12 : ℝ) • r a) =
          WildeQIT.partialTraceLeft ((E a ⊗ₖ (1 : Matrix Bool Bool ℂ)) * werner (5 / 12))) ∧
      HasLHSModel (werner (5 / 12)) := by sorry

end CompNonlocal
