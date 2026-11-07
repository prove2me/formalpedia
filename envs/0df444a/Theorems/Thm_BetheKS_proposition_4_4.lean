-- Prove2me | Theorems.Thm_BetheKS_proposition_4_4
-- name    : BetheKS.proposition_4_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:36:29.123696+00:00
-- url     : https://prove2.me/theorems/a6f42f7e-9327-41a2-88e8-20f62d98c667
-- title:
--   Proposition 4.4 — spectral gap of the transfer operator when $\kappa>\sqrt d\,c_\delta$
-- statement:
--   Fix $t\ge\sqrt d>1$ and $\delta>0$, and suppose the spectral radius $\kappa$ of $\mathcal L$ on $L^2(\Omega,\nu)$ satisfies $\kappa>\sqrt d\,c_\delta$. Then:
--
--   1. there are nonzero nonnegative right and left eigenfunctions $h,\ell\in L^2(\Omega)$ with
--   $$
--   \mathcal Lh=\kappa h,\qquad\mathcal L^*\ell=\kappa\ell;
--   $$
--   almost surely over $T\sim\nu$, $\ell(T)>0$, while $h(T)=0$ on finite trees and $h(T)>0$ on infinite trees;
--   2. $\kappa$ is an algebraically simple eigenvalue of $\mathcal L$;
--   3. $\kappa$ is the only point of $\sigma(\mathcal L)$ with absolute value $\kappa$;
--   4. there are $C<\infty$ and $0<\theta<1$ such that for every integer $L\ge0$
--   $$
--   \|\kappa^{-L}\mathcal L^L\mathbf 1-h\|_2\le C\theta^L .
--   $$
--
--   **Formalization Note** $L^2(\Omega)$ is complex (Definition A.2) and $\mathcal L^*$ is the Hilbert adjoint. "Nonnegative" means a.e. real and $\ge0$. "Algebraically simple" means the generalized eigenspace $\bigcup_k\ker(\mathcal L-\kappa)^k$ is one-dimensional.
--
--   Differences from the source:
--
--   - encoding: Ω the locally finite rooted trees, ν the Poi(d) Galton–Watson law → offspring functions on Ulam–Harris words (children ordered) with i.i.d. Poi(d) coordinates; reason: the tree read off has law ν and, given the root degree, the forward subtrees are i.i.d. ν, which is all the arguments use; κ, h, δ(μ) are unchanged
--   - reading: h in (4) and h in (1) → one h satisfying (1) and (4) together; reason: the proof normalizes the eigenfunction of (1) so that P1 = h (p.16); (1) fixes h only up to a positive factor
--   - encoding: κ is an algebraically simple eigenvalue of ℒ → the maximal generalized eigenspace ⨆ₖ ker(ℒ − κ)^k has finrank 1; reason: the definition of algebraic multiplicity for a bounded operator; finrank is 0 on an infinite-dimensional space, so the claim also excludes that case
-- source:
--   Dong, McKenzie, Bethe Hessian Recovery through the Kesten–Stigum Regime, arXiv:2610.41802 (held version, sha256 4da41e16…), Proposition 4.4, p.8 (PDF p.9); proof in App. B.1, pp.15–16

import Mathlib
import Definitions.Def_BetheKS_cavityIter
import Definitions.Def_BetheKS_transferOp

set_option autoImplicit false

open MeasureTheory Filter Topology
open scoped ENNReal

namespace BetheKS

/-- **Proposition 4.4** — Dong, McKenzie, arXiv:2610.41802 (held version, sha256 4da41e16…), p.8
(PDF p.9). Suppose the spectral radius `κ` of `ℒ` satisfies `κ > √d c_δ`. Then:
1. there are nonzero nonnegative right and left eigenfunctions `h, ℓ ∈ L²(Ω)` with `ℒh = κh`,
   `ℒ*ℓ = κℓ`; almost surely `ℓ(T) > 0`, while `h(T) = 0` on finite trees and `h(T) > 0` on infinite
   trees;
2. `κ` is an algebraically simple eigenvalue of `ℒ`;
3. `κ` is the only point of `σ(ℒ)` with absolute value `κ`;
4. there are `C < ∞` and `0 < θ < 1` with `‖κ^{−L} ℒ^L 1 − h‖₂ ≤ C θ^L` for every integer `L ≥ 0`.

Standing assumptions of §4: `t ≥ √d > 1`, `δ > 0`.

**Formalization Note.** `L²(Ω) = L²(Ω, ν; ℂ)` (Definition A.2). "Nonnegative" means `ν`-a.e. real
and `≥ 0`. `ℒ*` is the Hilbert adjoint. "Algebraically simple": the generalized eigenspace
`⋃ₖ ker(ℒ − κ)^k` is one-dimensional. In (4) the `h` is the one of (1), normalized (the paper's proof,
p.16: "We can normalize so that `P1 = h`"), so (1) and (4) are asserted for the same `h`. -/
theorem proposition_4_4 (d t δ : ℝ) (hd : 1 < d) (ht : Real.sqrt d ≤ t) (hδ : 0 < δ)
    (hκ : ENNReal.ofReal (Real.sqrt d * cDelta t δ) < kappa d t δ) :
    (∃ h ℓ : Lp ℂ 2 (gwLaw d),
      h ≠ 0 ∧ ℓ ≠ 0 ∧
      (∀ᵐ K ∂gwLaw d, 0 ≤ ((h : Offspring → ℂ) K).re ∧ ((h : Offspring → ℂ) K).im = 0) ∧
      (∀ᵐ K ∂gwLaw d, 0 ≤ ((ℓ : Offspring → ℂ) K).re ∧ ((ℓ : Offspring → ℂ) K).im = 0) ∧
      transferOp d t δ h = ((kappa d t δ).toReal : ℂ) • h ∧
      ContinuousLinearMap.adjoint (transferOp d t δ) ℓ = ((kappa d t δ).toReal : ℂ) • ℓ ∧
      (∀ᵐ K ∂gwLaw d, 0 < ((ℓ : Offspring → ℂ) K).re) ∧
      (∀ᵐ K ∂gwLaw d, IsFiniteTree K → (h : Offspring → ℂ) K = 0) ∧
      (∀ᵐ K ∂gwLaw d, ¬ IsFiniteTree K → 0 < ((h : Offspring → ℂ) K).re) ∧
      ∃ C θ : ℝ, 0 < θ ∧ θ < 1 ∧ ∀ L : ℕ,
        ‖(((kappa d t δ).toReal : ℂ)⁻¹ ^ L) • ((transferOp d t δ) ^ L) (oneL2 d) - h‖ ≤ C * θ ^ L) ∧
    Module.finrank ℂ ↥(Module.End.maxGenEigenspace (transferOp d t δ).toLinearMap
      ((kappa d t δ).toReal : ℂ)) = 1 ∧
    (∀ z ∈ spectrum ℂ (transferOp d t δ), (‖z‖₊ : ℝ≥0∞) = kappa d t δ → z = ((kappa d t δ).toReal : ℂ)) := by sorry

end BetheKS
