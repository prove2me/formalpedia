-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_3_3
-- name    : CosetTreeSVP.SVP.lemma_3_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:32:26.115192+00:00
-- url     : https://prove2.me/theorems/7a02cd13-9cdf-4217-ba44-3d5baeb56daf
-- title:
--   Lemma 3.3 — Σ_{x∈L∖{0}} (1 + ‖x‖/λ₁)^k ρ_σ(x) ≤ 2^{o(n)} (β²nσ²/(2πeλ₁²))^{n/2} when nσ²/λ₁² ≤ n^{O(1)}
-- statement:
--   **Lemma 3.3.** For every fixed integer $k \ge 0$ and every exponent $C_0$ there are $h$ with $h(n)/n \to 0$ and $n_0$ such that for all $n \ge n_0$, every full-rank lattice $L = B\mathbb Z^n$ and every $\sigma > 0$ with $n\sigma^2/\lambda_1(L)^2 \le n^{C_0}$,
--   $$\sum_{x\in L\setminus\{0\}}\Big(1+\frac{\|x\|}{\lambda_1(L)}\Big)^k\rho_\sigma(x) \le 2^{h(n)}\Big(\frac{\beta^2n\sigma^2}{2\pi e\lambda_1(L)^2}\Big)^{n/2}.$$
--   This is the paper's basic Gaussian-mass estimate, derived from the Kabatiansky–Levenshtein point count.
--
--   Differences from the source:
--   - encoding: 2^{o(n)} uniformly over L and σ with nσ²/λ² ≤ n^{O(1)} → for every exponent C₀: one h with h(n)/n → 0 and n₀, quantified after k and C₀ and before n, B, σ; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - reading: β = 2^{0.4014...}, the lattice-point constant of [KL78] and [PS09, Lemma 3]; t0 = β²/(4e ln 2) = 0.23147… → beta = 2^R with R = a log₂ a − b log₂ b, a = (1 + sin(π/3))/(2 sin(π/3)), b = (1 − sin(π/3))/(2 sin(π/3)); t0 = beta²/(4e ln 2); reason: the printed decimals pin the Kabatiansky–Levenshtein exponent at angle π/3: R = 0.401413…, t0 = 0.231470…, 1/(2√t0) = 1.039255…, all matching the paper
--   - encoding: a real series → a sum in [0, ∞] of the nonnegative terms; reason: same value for a sum of nonnegative terms
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 13 (PDF 15), Lemma 3.3

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_3_3 (k : ℕ) (C₀ : ℝ) :
    ∃ h : ℕ → ℝ, Tendsto (fun n => h n / n) atTop (𝓝 0) ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 → ∀ σ : ℝ, 0 < σ →
        (n : ℝ) * σ ^ 2 / SuperlatSVP.lam1 (SuperlatSVP.lat B) ^ 2 ≤ (n : ℝ) ^ C₀ →
        ∑' x : {x : E n // x ∈ SuperlatSVP.lat B ∧ x ≠ 0},
            ENNReal.ofReal ((1 + ‖(x : E n)‖ / SuperlatSVP.lam1 (SuperlatSVP.lat B)) ^ k *
              RegevLWE.GaussConv.rho σ (x : E n)) ≤
          ENNReal.ofReal ((2 : ℝ) ^ h n *
            (beta ^ 2 * n * σ ^ 2 /
              (2 * Real.pi * Real.exp 1 * SuperlatSVP.lam1 (SuperlatSVP.lat B) ^ 2)) ^
                ((n : ℝ) / 2)) := by sorry

end CosetTreeSVP.SVP
