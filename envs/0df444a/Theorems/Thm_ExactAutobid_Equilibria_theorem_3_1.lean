-- Prove2me | Theorems.Thm_ExactAutobid_Equilibria_theorem_3_1
-- name    : ExactAutobid.Equilibria.theorem_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T21:57:04.937532+00:00
-- url     : https://prove2.me/theorems/7909e712-5c32-4041-922c-c75ab0aa8f54
-- title:
--   Theorem 3.1 — exact arithmetic (gates C, D, ϕ) from a nonlinear response or from the throttling gate set
-- statement:
--   Let $h$ be continuous and strictly monotone on a rational interval $I_0 = [\mathrm{lo}, \mathrm{hi}]$, and let $J = [j_1, j_2]$ ($j_1 < j_2$ rational) lie in the interior of $h(I_0)$, with the inverse of $h$ on $J$ equal to the **nonaffine quadratic-over-linear** function
--   $$p(t) = \frac{a t^2 + b t + c}{d t + e},\qquad a,b,c,d,e \in \mathbb{Q},\quad dt + e \ne 0 \text{ on } J.$$
--   Then (i) the signed clipped affine expressions together with $h$, and (ii) complement, capped doubling, halving, capped addition and $I(x) = 1/(1+x)$ on $[0,1]$, each implement the source functions $C$, $D$, $\phi$ of Lemma 2.5 by fixed-size rational subcircuits: every source input in $[0,1]^k$ extends through the subcircuit, and every solution of its equations gives the required output.
--
--   Alternative (i) is used for ROI pacing and both GSP models, alternative (ii) for throttling.
--
--   Differences from the source:
--   - reading: signed clipped affine expressions → gates y = clip_[0,1](c + Σ_j a_j x_j) of any arity with rational coefficients of either sign, inputs any reals; reason: the proof composes affine expressions with h's outputs, which lie in h(I₀) rather than [0,1]
--   - reading: a response h on I₀ (clipping to I₀ implemented by an affine encoding of that interval into [0,1]) → the response gate y = h(lo + (hi − lo)s) with s ∈ [0,1]; reason: the paper's own description of how h is fed (proof of Theorem 3.1, p. 59)
--   - encoding: inverse on J is a nonaffine quadratic-over-linear function with rational coefficients and no pole on J → p(t) = (at² + bt + c)/(dt + e) with dt + e ≠ 0, p(t) ∈ I₀ and h(p(t)) = t for t ∈ J, and no affine function r t + s equals p on J; reason: explicit form of the hypothesis
--   - encoding: implements by fixed-size rational subcircuits → ImplementsOn: one finite subcircuit over the gate set; every input in [0,1]^k extends, every solution has the source output; reason: the implementation notion of the mission's Circuits definition
-- source:
--   Huang, Liu, Yan, On the Complexity of Exact Autobidding Equilibria, arXiv:2611.04475 (sha256 270d1b74…), p. 10 (PDF 12), Theorem 3.1

import Mathlib
import Definitions.Def_ExactAutobid_Equilibria_Circuits

namespace ExactAutobid.Equilibria

/-- **Theorem 3.1 (Exact Arithmetic from a Nonlinear Response).** (i) Signed clipped affine
expressions together with a continuous strictly monotone response `h` on `I₀ = [lo, hi]`, whose
inverse on a nondegenerate closed rational interval `J = [j₁, j₂] ⊂ int h(I₀)` is the nonaffine
quadratic-over-linear function `p(t) = (a t² + b t + c)/(d t + e)` with rational coefficients and no
pole on `J`, implement `C`, `D` and `ϕ` by fixed-size rational subcircuits; (ii) so do complement,
capped doubling, halving, capped addition and `I(x) = 1/(1 + x)` on `[0, 1]`. -/
theorem theorem_3_1 :
    (∀ (h : ℝ → ℝ) (lo hi j₁ j₂ a b c d e : ℚ),
      ContinuousOn h (Set.Icc (lo : ℝ) hi) →
      (StrictMonoOn h (Set.Icc (lo : ℝ) hi) ∨ StrictAntiOn h (Set.Icc (lo : ℝ) hi)) →
      j₁ < j₂ →
      Set.Icc (j₁ : ℝ) j₂ ⊆ interior (h '' Set.Icc (lo : ℝ) hi) →
      (∀ t ∈ Set.Icc (j₁ : ℝ) j₂, (d : ℝ) * t + e ≠ 0) →
      (∀ t ∈ Set.Icc (j₁ : ℝ) j₂,
        ((a : ℝ) * t ^ 2 + b * t + c) / (d * t + e) ∈ Set.Icc (lo : ℝ) hi ∧
        h (((a : ℝ) * t ^ 2 + b * t + c) / (d * t + e)) = t) →
      (¬ ∃ r s : ℝ, ∀ t ∈ Set.Icc (j₁ : ℝ) j₂,
        ((a : ℝ) * t ^ 2 + b * t + c) / (d * t + e) = r * t + s) →
      ImplementsOn (gatesResponse h lo hi) (unitCube 1) srcC ∧
        ImplementsOn (gatesResponse h lo hi) (unitCube 1) srcD ∧
        ImplementsOn (gatesResponse h lo hi) (unitCube 2) srcPhi) ∧
    (ImplementsOn gatesThrottle (unitCube 1) srcC ∧
      ImplementsOn gatesThrottle (unitCube 1) srcD ∧
      ImplementsOn gatesThrottle (unitCube 2) srcPhi) := by sorry

end ExactAutobid.Equilibria
