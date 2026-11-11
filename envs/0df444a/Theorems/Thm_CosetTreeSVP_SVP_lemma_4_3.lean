-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_4_3
-- name    : CosetTreeSVP.SVP.lemma_4_3
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:33:27.602556+00:00
-- url     : https://prove2.me/theorems/9fe1720c-51ff-4ab7-8076-b06bd4288368
-- title:
--   Lemma 4.3 — except with probability o(1) over U and δ, A_δ(θ*) = c_δG(w)f(w)^{p−1} + e_δ with |c_δ| = 1 and ‖e_δ‖ ≤ (s²λ/q)2^{−n/4−Ω(n)}
-- statement:
--   Let $L = B\mathbb Z^n$ for a nonsingular $B \in \mathbb R^{n\times n}$, $\lambda = \lambda_1(L)$, and let $s = \sqrt{4nt\ln 2/(\pi d^2)}$, $g = \tfrac12\log_2(t/t_0)$ with $t_0 = \beta^2/(4e\ln 2)$. Let $p, q, m, Q, N$ be the parameters of Eq. (17) and §4.3, $v$ a shortest vector of $L$, $w = B^{-1}v \bmod q$, $U$ uniform in $GL_n(\mathbb F_q)$, $\delta$ uniform, $k^* = U^{-T}w$, $\theta^* = (k^*)_{H_m}$, $\alpha^*_{j,a} = \varepsilon_{a2^j}(k^*)_{H_j}$. $A_\delta(\theta)$ is the target of Eq. (27).
--
--   **Lemma 4.3.** Fix $t_0 < t < 1/4$. There are $c > 0$, $\varepsilon(n) \to 0$ and $n_0$ such that for all $n \ge n_0$, every nonsingular $B$, every $d$ with $\lambda \le d \le (1+1/n)\lambda$ and every shortest vector $v$ with $\lambda = \|v\|$, except with probability at most $\varepsilon(n)$ over $(U, \delta)$ there are $c_\delta \in \mathbb C$ and $e_\delta \in \mathbb C^n$ with
--   $$A_\delta(\theta^*) = c_\delta\,G(w)f(w)^{p-1} + e_\delta,\qquad |c_\delta| = 1,\qquad \|e_\delta\| \le \frac{s^2\lambda}{q}2^{-n/4-cn}.$$
--   The ideal target already points along $v$ at the right $\theta$.
--
--   Differences from the source:
--   - encoding: o(1) and 2^{−Ω(n)} → ε(n) → 0, c > 0 and n₀ chosen after t and before n, B, d, v; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - reading: the lemma does not restate λ ≤ d ≤ (1 + 1/n)λ and t0 < t < 1/4 → hypotheses t0 < t < 1/4 and λ₁(L) ≤ d ≤ (1 + 1/n)λ₁(L); reason: standing assumptions of §3 (p. 12: 'fix t0 < t < 1/4', 'in most of our analysis we assume λ ≤ d ≤ (1 + 1/n)λ'); s, and hence f, G, A_δ, Â_δ, are defined from t and d, and the proof uses Lemma 4.5/4.6, which assume them
--   - reading: β = 2^{0.4014...}, the lattice-point constant of [KL78] and [PS09, Lemma 3]; t0 = β²/(4e ln 2) = 0.23147… → beta = 2^R with R = a log₂ a − b log₂ b, a = (1 + sin(π/3))/(2 sin(π/3)), b = (1 − sin(π/3))/(2 sin(π/3)); t0 = beta²/(4e ln 2); reason: the printed decimals pin the Kabatiansky–Levenshtein exponent at angle π/3: R = 0.401413…, t0 = 0.231470…, 1/(2√t0) = 1.039255…, all matching the paper
--   - encoding: p, q, m, N of Eq. (17) (undefined while n/log³ n < 1) → pN n = 2^{⌊log₂ ⌊n/ln³ n⌋⌋}, qN n = least prime > 2√p, mN n = log₂ p + 1, QN n = q^{⌊n/m⌋}, NN n = Q p⁴; statements for n ≥ n₀; reason: Eq. (17) literally; for small n the values are placeholders and n₀ is quantified with the other constants
--   - generalization: m = log₂ p + 1 is assumed to divide n, and H_j is the j-th block of n/m coordinates (p. 16) → every n ≥ n₀, with footnote 7's blocks: blocks 1, …, m−1 of ℓ = ⌊n/m⌋ coordinates and block m of the remaining n − (m−1)ℓ; Q = q^ℓ; reason: footnote 7 gives this decomposition for all n; when m | n it is exactly the main text's, so the Lean statement specializes to the printed one
--   - encoding: f(w) = F_{1/s}(Bw/q), G(w) = ∇F_{1/s}(Bw/q) (Eqs. (9)–(11)) → fq, Gq by the primal series of Eqs. (9), (10) at Bw/q, w lifted to {0, …, q−1}ⁿ; reason: the paper's own first representations; periodicity makes the value independent of the lift, and the series is the termwise derivative
--   - encoding: the conditional expectation E[· | U, δ] of Eq. (27) → an unconditional sum over (L*)^p weighted by ∏_r D_{L*,s}(X_r), for fixed U, δ; reason: the samples are independent of U and δ
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 17 (PDF 19), Lemma 4.3

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics
import Definitions.Def_CosetTreeSVP_SVP_Tree

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_4_3 (t : ℝ) (ht0 : t0 < t) (ht1 : t < 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 →
      ∀ d : ℝ, SuperlatSVP.lam1 (SuperlatSVP.lat B) ≤ d →
        d ≤ (1 + 1 / (n : ℝ)) * SuperlatSVP.lam1 (SuperlatSVP.lat B) →
      ∀ v : E n, IsShortestVec (SuperlatSVP.lat B) v →
        prUDelta (p := pN n) (m := mN n)
          {Uδ | ¬ ∃ (cδ : ℂ) (e : CE n),
              Adelta (QN n) B (sPar n t d) Uδ.1 Uδ.2
                  (thetaStar (mN n) Uδ.1 (coeffMod B (qN n) v)) =
                (cδ * ((fq B (qN n) (sPar n t d) (coeffMod B (qN n) v) ^ (pN n - 1) : ℝ) : ℂ)) •
                    toC (Gq B (qN n) (sPar n t d) (coeffMod B (qN n) v)) + e ∧
              ‖cδ‖ = 1 ∧
              ‖e‖ ≤ sPar n t d ^ 2 * ‖v‖ / (qN n : ℝ) * (2 : ℝ) ^ (-((n : ℝ) / 4) - c * n)} ≤
          ENNReal.ofReal (ε n) := by sorry

end CosetTreeSVP.SVP
