-- Prove2me | Theorems.Thm_BoundEntGauss_bound_entangled_gaussian_family
-- name    : BoundEntGauss.bound_entangled_gaussian_family
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:49:58.758242+00:00
-- url     : https://prove2.me/theorems/ad10e4f3-f346-436c-8766-0f978bce6533
-- title:
--   Section IV, Eq. (11) — for $a<ce$, Gaussian states with covariance $\gamma(a,b,c,e,f)$ exist and are ppt but not separable
-- statement:
--   Consider two oscillator modes held by Alice and two held by Bob. Let $a,b,c,e,f>0$ with $a<ce$, and let $\gamma=\gamma(a,b,c,e,f)$ be the $8\times8$ covariance matrix of the five-parameter family of Eq. (11). Then:
--
--   1. for every mean vector $d\in\mathbb R^8$ there is a Gaussian density operator $\rho$ on the Fock space of the four modes with covariance $\gamma$ and mean $d$;
--   2. every Gaussian density operator $\rho$ with covariance $\gamma$ (and any mean) has positive partial transpose and is not separable:
--   $$
--   \rho^{T_A}\ \text{is a density operator}\qquad\text{and}\qquad \rho\notin\overline{\operatorname{conv}}\{\rho_A\otimes\rho_B\}.
--   $$
--
--   This is the paper's main result: for $2\times2$ modes, positivity of the partial transpose does not imply separability of Gaussian states, in contrast to the $1\times N$ case. The family consists of bound entangled Gaussian states, i.e. entangled states with positive partial transpose, which by Horodecki et al. cannot be distilled.
--
--   Differences from the source:
--   - reading: "bound entangled" → IsPPTState ρ ∧ ¬ IsSeparable ρ.coefficients; reason: the paper establishes exactly these two properties; non-distillability of ppt states is cited from Horodecki et al. [3] and not proved in the paper
--   - reading: the family (11), a, b, …, f > 0, with γ + iσ ≥ 0 → a, b, c, e, f > 0 and a < c·e (d eliminated); reason: the paper shows γ + iσ ≥ 0 iff a ≤ ce with equality ruled out, and d = (bc+f)/a
--   - reading: "separable" (no definition in the paper) → trace-norm closed convex hull of product states (Holevo–Shirokov–Werner, published IsSeparable); reason: the standard definition for infinite-dimensional systems; it contains every finite, countable and integral mixture of product states
--   - reading: "has positive partial transpose" → IsPPTState: the Fock-basis partial transpose on Alice's factor is a density operator (trace class, positive, trace one); reason: the paper's own phrasing "the partial transpose of ρ is again a density operator" (p. 3)
--   - reading: Gaussian state: tr[ρW(ξ)] = exp(imᵀξ − ¼ξᵀγξ), Eq. (3), with W(ξ) = exp(iξ·σ·R) → HasGaussianCovariance: characteristic function exp(−¼ξᵀσᵀγσξ + iξᵀσd) on actual Fock-space densities, every mean d; reason: as printed, (3) is consistent with W(ξ) = exp(iξ·σ·R) only if σγσᵀ = γ; the paper states that γ and m are the covariance and mean of ρ, which the Lean form makes true
--   - encoding: γ defined by the construction γ = ΛΩ⁻¹ from Ω₁ of (11), with d = (bc+f)/a → the closed form wwGamma a b c e f, tied to the construction by the milestone family_construction; reason: an explicit matrix instead of an opaque inverse; same matrix
--   - encoding: two canonical degrees of freedom on each side → QuadratureIndex 2 ⊕ QuadratureIndex 2 (interleaved (x_j, p_j), Alice = Sum.inl), Fock space indexed by Occupation (Fin 2) × Occupation (Fin 2); reason: Lean representation of the same objects
-- source:
--   Werner, Wolf, Bound entangled Gaussian states, arXiv:quant-ph/0009118v1, Section IV, Eq. (11), p. 4; abstract, p. 1

import Mathlib
import Definitions.Def_BoundEntGauss_IsPPTState
import Definitions.Def_BoundEntGauss_wwGamma

open QAlgorithms.Papers.Independent.Dependency50.P33 (State IsSeparable)
open QAlgorithms.Papers.Independent.Frontier30.P08 (QuadratureIndex)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Intakenext100.P68 (HasGaussianCovariance)

namespace BoundEntGauss

/-- **A five-parameter family of bound entangled Gaussian states (2 × 2 modes).**
Werner, Wolf, *Bound entangled Gaussian states*, arXiv:quant-ph/0009118v1, Section IV, Eq. (11), p. 4 ("States obtained from (11) are all of a non block diagonal form
similar to (9), and are hence bound entangled."), and the abstract, p. 1.

Let `a, b, c, e, f > 0` with `a < c·e`, and let `γ = γ(a, b, c, e, f)` be the covariance matrix
of Eq. (11) on two modes for Alice and two modes for Bob.

1. For every mean vector `d ∈ ℝ⁸` there is a Gaussian density operator with covariance `γ` and
   mean `d`.
2. Every Gaussian density operator with covariance `γ` (and any mean) has positive partial
   transpose and is not separable.

**Formalization Note.** Reading: "bound entangled" is "ppt and entangled" — the paper's argument
establishes exactly these two properties (non-distillability of ppt states is cited from
Horodecki et al. [3]). Separability is the trace-norm closed convex hull of product states
(`Dependency50.P33.IsSeparable`), ppt is `IsPPTState` (the Fock-basis partial transpose on Alice
is a density operator), and "Gaussian with covariance `γ` and mean `d`" is the published
`HasGaussianCovariance`. Clause 1 makes clause 2 non-vacuous. -/
theorem bound_entangled_gaussian_family (a b c e f : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (he : 0 < e) (hf : 0 < f) (hace : a < c * e) :
    (∀ d : QuadratureIndex 2 ⊕ QuadratureIndex 2 → ℝ,
        ∃ ρ : State (Occupation (Fin 2) × Occupation (Fin 2)),
          HasGaussianCovariance ρ (wwGamma a b c e f) d) ∧
    ∀ (ρ : State (Occupation (Fin 2) × Occupation (Fin 2)))
        (d : QuadratureIndex 2 ⊕ QuadratureIndex 2 → ℝ),
        HasGaussianCovariance ρ (wwGamma a b c e f) d →
        IsPPTState ρ ∧ ¬ IsSeparable ρ.coefficients := by sorry

end BoundEntGauss
