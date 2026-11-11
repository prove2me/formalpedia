-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_4_6
-- name    : CosetTreeSVP.SVP.lemma_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:33:24.200129+00:00
-- url     : https://prove2.me/theorems/7dc2f9df-356e-45ae-9a58-f8deeaaf2fec
-- title:
--   Lemma 4.6 — except with probability 2^{−Ω(n)} over U, for every θ ∈ H_m, E_{δ,X}[‖Â_δ(θ) − A_δ(θ)‖² | U] ≤ (s²λ/q)² Q^{−1} 2^{o(n)}
-- statement:
--   Let $L = B\mathbb Z^n$ for a nonsingular $B \in \mathbb R^{n\times n}$, $\lambda = \lambda_1(L)$, and let $s = \sqrt{4nt\ln 2/(\pi d^2)}$, $g = \tfrac12\log_2(t/t_0)$ with $t_0 = \beta^2/(4e\ln 2)$. Let $p, q, m, Q, N$ be the parameters of Eq. (17) and §4.3, $v$ a shortest vector of $L$, $w = B^{-1}v \bmod q$, $U$ uniform in $GL_n(\mathbb F_q)$, $\delta$ uniform, $k^* = U^{-T}w$, $\theta^* = (k^*)_{H_m}$, $\alpha^*_{j,a} = \varepsilon_{a2^j}(k^*)_{H_j}$. $\hat A_\delta(\theta)$ is the estimator of Eq. (33) from independent samples $X_{r,i} \sim D_{L^*,s}$, $r \in [0,p)$, $i \in [N]$.
--
--   **Lemma 4.6.** Fix $t_0 < t < 1/4$. There are $c > 0$, a function $h$ with $h(n)/n \to 0$ and $n_0$ such that for all $n \ge n_0$, every nonsingular $B$ and every $d$ with $\lambda \le d \le (1+1/n)\lambda$, except with probability at most $2^{-cn}$ over $U$, simultaneously for every $\theta \in H_m$
--   $$\mathbb E_{\delta,X}\big[\|\hat A_\delta(\theta) - A_\delta(\theta)\|^2 \,\big|\, U\big] \le \Big(\frac{s^2\lambda}{q}\Big)^2Q^{-1}2^{h(n)}.$$
--   The estimator's variance is a $Q^{-1}$ fraction of the signal.
--
--   Differences from the source:
--   - encoding: 2^{−Ω(n)} and 2^{o(n)} → c > 0, h with h(n)/n → 0 and n₀ chosen after t and before n, B, d; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - reading: t is not restated (only λ ≤ d ≤ (1 + 1/n)λ is) → hypothesis t0 < t < 1/4; reason: standing assumption of §3 (p. 12, 'fix t0 < t < 1/4'), on which s and g depend
--   - reading: β = 2^{0.4014...}, the lattice-point constant of [KL78] and [PS09, Lemma 3]; t0 = β²/(4e ln 2) = 0.23147… → beta = 2^R with R = a log₂ a − b log₂ b, a = (1 + sin(π/3))/(2 sin(π/3)), b = (1 − sin(π/3))/(2 sin(π/3)); t0 = beta²/(4e ln 2); reason: the printed decimals pin the Kabatiansky–Levenshtein exponent at angle π/3: R = 0.401413…, t0 = 0.231470…, 1/(2√t0) = 1.039255…, all matching the paper
--   - encoding: p, q, m, N of Eq. (17) (undefined while n/log³ n < 1) → pN n = 2^{⌊log₂ ⌊n/ln³ n⌋⌋}, qN n = least prime > 2√p, mN n = log₂ p + 1, QN n = q^{⌊n/m⌋}, NN n = Q p⁴; statements for n ≥ n₀; reason: Eq. (17) literally; for small n the values are placeholders and n₀ is quantified with the other constants
--   - generalization: m = log₂ p + 1 is assumed to divide n, and H_j is the j-th block of n/m coordinates (p. 16) → every n ≥ n₀, with footnote 7's blocks: blocks 1, …, m−1 of ℓ = ⌊n/m⌋ coordinates and block m of the remaining n − (m−1)ℓ; Q = q^ℓ; reason: footnote 7 gives this decomposition for all n; when m | n it is exactly the main text's, so the Lean statement specializes to the printed one
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 19 (PDF 21), Lemma 4.6

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics
import Definitions.Def_CosetTreeSVP_SVP_Tree

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_4_6 (t : ℝ) (ht0 : t0 < t) (ht1 : t < 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ h : ℕ → ℝ, Tendsto (fun n => h n / n) atTop (𝓝 0) ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 →
      ∀ d : ℝ, SuperlatSVP.lam1 (SuperlatSVP.lat B) ≤ d →
        d ≤ (1 + 1 / (n : ℝ)) * SuperlatSVP.lam1 (SuperlatSVP.lat B) →
        prU {U : Matrix.GeneralLinearGroup (Fin n) (ZMod (qN n)) |
            ¬ ∀ θ : Fin n → ZMod (qN n), InH (mN n) (mN n) θ →
              expDeltaX (p := pN n) (m := mN n) (N := NN n) B (sPar n t d)
                  (fun δ X => ENNReal.ofReal
                    (‖Ahat (QN n) B U δ (fun r i => (X r i : E n)) θ -
                      Adelta (QN n) B (sPar n t d) U δ θ‖ ^ 2)) ≤
                ENNReal.ofReal ((sPar n t d ^ 2 * SuperlatSVP.lam1 (SuperlatSVP.lat B) /
                  (qN n : ℝ)) ^ 2 * (QN n : ℝ)⁻¹ * (2 : ℝ) ^ h n)} ≤
          ENNReal.ofReal ((2 : ℝ) ^ (-(c * n))) := by sorry

end CosetTreeSVP.SVP
