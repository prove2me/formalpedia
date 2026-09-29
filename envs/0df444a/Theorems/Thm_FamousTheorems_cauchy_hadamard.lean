-- Prove2me | Theorems.Thm_FamousTheorems_cauchy_hadamard
-- name    : FamousTheorems.cauchy_hadamard
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-23T17:14:03.591975+00:00
-- url     : https://prove2.me/theorems/5e0ac40c-e128-43a0-939a-017794218f6c
-- title:
--   The Cauchy–Hadamard theorem
-- statement:
--   **The Cauchy–Hadamard theorem.** The radius of convergence $\rho$ of a power series $\sum_n p_n$ (with $p_n$ continuous $n$-multilinear maps between normed spaces) satisfies
--   $$\frac1\rho=\limsup_{n\to\infty}\|p_n\|^{1/n}.$$
--
--   For scalar series $\sum a_nz^n$ this is the classical formula $1/\rho=\limsup|a_n|^{1/n}$. It determines exactly where a power series converges and is the basic link between the growth of coefficients and analyticity.
--
--   **Formalization note.** Mathlib's `FormalMultilinearSeries.radius_inv_eq_limsup`, with the radius in `ℝ≥0∞` (so $1/0=\infty$ and $1/\infty=0$) and `‖p n‖₊` the operator norm.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `FormalMultilinearSeries.radius_inv_eq_limsup`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem cauchy_hadamard {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius⁻¹ = Filter.limsup (fun n : ℕ => ((‖p n‖₊ ^ (1 / (n : ℝ)) : NNReal) : ENNReal)) Filter.atTop := by sorry

end FamousTheorems
