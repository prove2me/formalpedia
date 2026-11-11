-- Prove2me | Theorems.Thm_DetConnSketch_Main_theorem_8_2
-- name    : DetConnSketch.Main.theorem_8_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:42:59.427918+00:00
-- url     : https://prove2.me/theorems/cd9533a0-3406-4642-bc96-10f326a02407
-- title:
--   Theorem 8.2 — uniform positivity: $\varphi_S(\theta)\ge\frac14\exp(-64a^2k/\log(4k))>0$ at $\theta=a/(\sqrt k\log(4k))$, $a=10^{-7}$
-- statement:
--   Let $a = 10^{-7}$. For every positive integer $k$ and every sign matrix $S \in \{-1,1\}^{k\times k}$, put $\theta = \dfrac{a}{\sqrt k\,\log(4k)}$ (natural logarithm). Then
--   $$\varphi_S(\theta) \ge \frac14 \exp\!\Big(-\frac{64a^2k}{\log(4k)}\Big) > 0. \tag{3}$$
--   The bound is uniform: it holds for every one of the $2^{k^2}$ sign matrices, not on average.
--
--   It is the analytic core of the $\tilde\Omega(n^{3/2})$ lower bound (proved in Appendix A, pp. 60–97).
--
--   Differences from the source:
--   - encoding: ϕ_S(θ) ≥ (1/4) exp(−64a²k / log(4k)) → ((1/4) exp(…) : ℂ) ≤ charFun S θ in Mathlib's ℂ order (real parts ordered, imaginary parts equal); reason: φ_S : ℝ → ℂ (§8.1); the order also records that φ_S(θ) is real, as the paper states
--   - encoding: a = 10^{−7}, log → (1 : ℝ) / 10^7, Real.log (natural); reason: Appendix A works in nats (p. 63, p. 97)
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), p. 48 (PDF 52), Theorem 8.2

import Mathlib
import Definitions.Def_DetConnSketch_Main_Signs
import Definitions.Def_DetConnSketch_Main_CharFun

open scoped ComplexOrder

namespace DetConnSketch.Main

/-- Theorem 8.2 (uniform positivity of the characteristic function): for `a = 10^{-7}`, every
positive integer `k` and every sign matrix `S ∈ {−1, 1}^{k×k}`, with `θ = a / (√k log(4k))`
(natural logarithm), `φ_S(θ) ≥ (1/4) exp(−64 a² k / log(4k)) > 0`. The inequality is in `ℂ`'s
order, so it also asserts that `φ_S(θ)` is real. -/
theorem theorem_8_2 (k : ℕ) (hk : 1 ≤ k) (S : Matrix (Fin k) (Fin k) ℝ) (hS : IsSignMatrix S) :
    ((((1 : ℝ) / 4) * Real.exp (-(64 * ((1 : ℝ) / 10 ^ 7) ^ 2 * k) / Real.log (4 * k)) : ℝ) : ℂ) ≤
        charFun S (((1 : ℝ) / 10 ^ 7) / (Real.sqrt k * Real.log (4 * k))) ∧
      (0 : ℝ) < ((1 : ℝ) / 4) * Real.exp (-(64 * ((1 : ℝ) / 10 ^ 7) ^ 2 * k) / Real.log (4 * k)) := by sorry

end DetConnSketch.Main
