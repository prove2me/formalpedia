-- Prove2me | Theorems.Thm_ConstDepthUnitary_poisson_half_integer_lattice
-- name    : ConstDepthUnitary.poisson_half_integer_lattice
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:44:59.777107+00:00
-- url     : https://prove2.me/theorems/c7258884-4816-4d56-aad7-ed990945fd0e
-- title:
--   Lemma 3.2 (absolute convergence) and Eq. (19) — Poisson summation on the half-integer lattice
-- statement:
--   Let $f$ be a Schwartz function on $\mathbb R^N$ and $\Delta>0$. With $F_{2\pi}f(v)=\int f(u)e^{-2\pi iu^{\mathsf T}v}du$ and $F$ the Fourier transform without $2\pi$ in the exponent, the sums $\sum_{w\in\mathbb Z^N}f(w)$ and $\sum_{w\in\mathbb Z^N}F_{2\pi}f(w)$ converge absolutely, and on the rescaled half-integer lattice
--   $$\frac{\Delta^N}{(2\pi)^{N/2}}\sum_{w\in\mathbb Z^N}f\Bigl(\bigl(w+\tfrac12\mathbf 1\bigr)\Delta\Bigr)=\sum_{w\in\mathbb Z^N}(-1)^{\sum_j w_j}(Ff)\Bigl(\frac{2\pi}{\Delta}w\Bigr),$$
--   with both of these sums absolutely convergent as well. This is the form of Poisson summation that the sampling lemma on the grid rests on.
--
--   **Formalization Note** Mathlib's `𝓕` is $F_{2\pi}$. The identity (16) itself is the published `SchwartzMap.tsum_eq_tsum_fourier_euclideanSpace`, which has no convergence clause.
--
--   Differences from the source:
--   - encoding: the sums in (19) stated without a convergence clause → absolute summability of both sums of (19) in the conclusion; reason: a Lean infinite sum of a non-summable family is 0, and for Schwartz f convergence holds
-- source:
--   Nehoran, Slote, Yuen, All Unitaries Have Constant Depth Quantum Circuits, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.2 and Eq. (19), p.17

import Mathlib
import Definitions.Def_ConstDepthUnitary_latticePt
import Definitions.Def_ConstDepthUnitary_contF
open scoped SchwartzMap FourierTransform

namespace ConstDepthUnitary

/-- Lemma 3.2, last sentence (both Poisson sums converge absolutely), and Eq. (19), the Poisson summation
formula on the rescaled half-integer lattice:
`Δ^N/(2π)^{N/2} Σ_{w ∈ ℤ^N} f((w + ½·1)Δ) = Σ_{w ∈ ℤ^N} (−1)^{Σ_j w_j} (F f)(2π/Δ · w)`, with both of its sums
absolutely convergent.

Nehoran, Slote, Yuen, *All Unitaries Have Constant Depth Quantum Circuits*, arXiv:2609.40351 (version of 2026-11-03, sha256 45cfb6a7…), Lemma 3.2 and Eq. (19), p.17. -/
theorem poisson_half_integer_lattice {N : ℕ} (f : 𝓢(EuclideanSpace ℝ (Fin N), ℂ)) (Δ : ℝ) (hΔ : 0 < Δ) :
    Summable (fun w : Fin N → ℤ => ‖f (latticePt w)‖) ∧
    Summable (fun w : Fin N → ℤ => ‖𝓕 f (latticePt w)‖) ∧
    Summable (fun w : Fin N → ℤ => ‖f (halfLatticePt Δ w)‖) ∧
    Summable (fun w : Fin N → ℤ => ‖contF f ((2 * Real.pi / Δ) • latticePt w)‖) ∧
    ((Δ ^ N / (2 * Real.pi) ^ ((N : ℝ) / 2) : ℝ) : ℂ) * ∑' w : Fin N → ℤ, f (halfLatticePt Δ w) =
      ∑' w : Fin N → ℤ, (-1 : ℂ) ^ (∑ j, w j) * contF f ((2 * Real.pi / Δ) • latticePt w) := by sorry

end ConstDepthUnitary
