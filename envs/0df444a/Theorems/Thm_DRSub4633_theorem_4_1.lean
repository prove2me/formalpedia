-- Prove2me | Theorems.Thm_DRSub4633_theorem_4_1
-- name    : DRSub4633.theorem_4_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:11:39.883454+00:00
-- url     : https://prove2.me/theorems/3d5f5c71-e5be-4dd3-957e-110af71ace11
-- title:
--   Theorem 4.1 — affine comparison on the cube with $\Gamma=1/\alpha_0$
-- statement:
--   Let $Q=[0,1]^n$, $\Gamma=1+b+1/(4b)=117486474169/54440750000$, $h$ the recovery map (9) and $g(f,x)$ the comparison field (24). For every nonnegative, continuously differentiable, DR-submodular $f:Q\to\mathbb R$,
--   $$f(o)\le\Gamma f(h(x))+\langle g(f,x),\,o-x\rangle\qquad(x,o\in Q).\tag{25}$$
--   For fixed $x$, $g(f,x)$ is linear in $f$. Both $h$ and $g(f,\cdot)$ are Borel measurable.
--
--   Equivalently $\alpha_0f(o)-f(h(x))\le\alpha_0\langle g(f,x),o-x\rangle$ with $\alpha_0=\Gamma^{-1}>0.4633$: a single vector, independent of the comparator, certifies the approximation coefficient $\alpha_0$. Through online-to-offline reductions this gives the paper's online and offline $\alpha_0$-approximations.
--
--   Differences from the source:
--   - reading: for fixed x, g(f, x) is linear in f → for x ∈ Q, field (a f₁ + c f₂) x = a field f₁ x + c field f₂ x for f₁, f₂ continuously differentiable on Q; reason: (24) is defined for every C^1 f (Section 5.1, (73)); additivity and real homogeneity on that space is linearity, and it implies the statement on the cone of nonnegative DR-submodular objectives
--   - reading: g(f, ·) is Borel measurable → the restriction of x ↦ field f x to the cube Q is measurable; reason: the field is defined for states in the cube; the proof (p.27) partitions the state cube
--   - generalization: h Borel measurable (h defined on Q) → hRec measurable on all of ℝ^n; reason: hRec is the total extension of (9); measurability on ℝ^n implies it on Q
--   - encoding: objective defined on Q only; R^n with coordinatewise order; C^1 with boundary derivatives the continuous extensions of interior ones → f a total function on EuclideanSpace ℝ (Fin n), hypotheses on the cube only, values off the cube never read; the order written coordinatewise; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, fderivWithin the cube); reason: Lean convention; on the cube the within-cube derivative of a C^1 function is the continuous extension of the interior derivative, so the instances are the same
--   - encoding: L includes a dummy coordinate of state 1, label 1, weight q = 1, zero field component → only the original coordinates are represented; the dummy enters as label 1 with q_1 = 1 and its zero terms are dropped; reason: F does not depend on the dummy coordinate (p.10), so every dropped term is zero; same instances
--   - encoding: coordinates [n] = {1, …, n}, ties broken by index → Fin n (0-based), ties broken by the order of Fin n; reason: Lean convention; same orders
--   - encoding: z the unique root of ∫_0^z e^{-st} ρ₁ = 1; ∫_0^1 J(t) dt of a vector → z as sInf of {t ∈ [0,1] : ∫_0^t e^{-sr} ρ₁ ≥ 1}; the integral taken coordinatewise; reason: the integral is continuous and strictly increasing, so the infimum is the root; coordinatewise integration of an integrable vector function is its integral
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Theorem 4.1, p.13

import Mathlib
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_DRSub4633_field
import Definitions.Def_DRSub4633_hRec
import Definitions.Def_DRSub4633_Gam

namespace DRSub4633

/-- **Theorem 4.1 (Affine comparison on the cube).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Theorem 4.1, p.13: "For every
nonnegative continuously differentiable DR-submodular `f : Q → ℝ`, the field `g(f, x)` in (24)
satisfies `f(o) ≤ Γf(h(x)) + ⟨g(f, x), o − x⟩` (`x, o ∈ Q`). (25) For fixed `x`, `g(f, x)` is linear
in `f`. Both `h` and `g(f, ·)` are Borel measurable."

Here `Γ = 1 + b + 1/(4b) = 117486474169/54440750000` (8), `h` is the recovery map (9) and `g` the
field (24).

**Formalization Note.** `Q = [0, 1]^n ⊆ EuclideanSpace ℝ (Fin n)`, every `n`. Continuously
differentiable DR-submodular is `GeomDRSub.IsDRSubmodular` (`C¹` on the cube, derivatives within
the cube). Linearity in `f` is additivity and real homogeneity, for every `x ∈ Q`, over functions
continuously differentiable on `Q` (the domain on which (24) is defined). Measurability of
`g(f, ·)` is of its restriction to the state cube `Q`; `h` is measurable on all of `ℝⁿ`. -/
theorem theorem_4_1 {n : ℕ} :
    (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, (∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) →
      GeomDRSub.IsDRSubmodular f →
      ∀ x ∈ GeomDRSub.cube n, ∀ o ∈ GeomDRSub.cube n,
        f o ≤ Gam * f (hRec x) + inner ℝ (field f x) (o - x)) ∧
    (∀ x ∈ GeomDRSub.cube n, ∀ (a c : ℝ) (f₁ f₂ : EuclideanSpace ℝ (Fin n) → ℝ),
      ContDiffOn ℝ 1 f₁ (GeomDRSub.cube n) → ContDiffOn ℝ 1 f₂ (GeomDRSub.cube n) →
      field (a • f₁ + c • f₂) x = a • field f₁ x + c • field f₂ x) ∧
    Measurable (hRec : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) ∧
    (∀ f : EuclideanSpace ℝ (Fin n) → ℝ, (∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) →
      GeomDRSub.IsDRSubmodular f →
      Measurable ((GeomDRSub.cube n).domRestrict (field f))) := by sorry

end DRSub4633
