-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_4_9
-- name    : CosetTreeSVP.SVP.lemma_4_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:33:34.130887+00:00
-- url     : https://prove2.me/theorems/74d75d4e-a1c7-4a50-ab84-d6d9542ff27d
-- title:
--   Lemma 4.9 — except with probability 2^{−Ω(n)} over U, ρ_{σ_j}(K_j∖{0}) and ρ_{σ_j/√(1−1/n)}(K_j∖{0}) are ≤ 2^{−(g/2−o(1))n} for all j < m
-- statement:
--   Let $L = B\mathbb Z^n$ for a nonsingular $B \in \mathbb R^{n\times n}$, $\lambda = \lambda_1(L)$, and let $s = \sqrt{4nt\ln 2/(\pi d^2)}$, $g = \tfrac12\log_2(t/t_0)$ with $t_0 = \beta^2/(4e\ln 2)$. Let $p, q, m$ be the parameters of Eq. (17), $U$ uniform in $GL_n(\mathbb F_q)$, and $K_j$, $\sigma_j = q/(2^{j/2}s)$ as in Eq. (38).
--
--   **Lemma 4.9.** Fix $t_0 < t < 1/4$. There are $c > 0$, $\varepsilon(n) \to 0$ and $n_0$ such that for all $n \ge n_0$, every nonsingular $B$ and every $d$ with $\lambda \le d \le (1+1/n)\lambda$, except with probability at most $2^{-cn}$ over $U$, for every $j \in \{0,\dots,m-1\}$
--   $$\rho_{\sigma_j}(K_j\setminus\{0\}) \le 2^{-(g/2-\varepsilon(n))n},\qquad \rho_{\sigma_j/\sqrt{1-1/n}}(K_j\setminus\{0\}) \le 2^{-(g/2-\varepsilon(n))n}.\tag{39}$$
--   These Gaussian-mass bounds drive the analysis of Lemmas 4.5 and 4.6.
--
--   Differences from the source:
--   - encoding: 2^{−Ω(n)} and o(1) → c > 0, ε(n) → 0 and n₀ chosen after t and before n, B, d; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - reading: t is not restated (only λ ≤ d ≤ (1 + 1/n)λ is) → hypothesis t0 < t < 1/4; reason: standing assumption of §3 (p. 12, 'fix t0 < t < 1/4'), on which s and g depend
--   - reading: β = 2^{0.4014...}, the lattice-point constant of [KL78] and [PS09, Lemma 3]; t0 = β²/(4e ln 2) = 0.23147… → beta = 2^R with R = a log₂ a − b log₂ b, a = (1 + sin(π/3))/(2 sin(π/3)), b = (1 − sin(π/3))/(2 sin(π/3)); t0 = beta²/(4e ln 2); reason: the printed decimals pin the Kabatiansky–Levenshtein exponent at angle π/3: R = 0.401413…, t0 = 0.231470…, 1/(2√t0) = 1.039255…, all matching the paper
--   - encoding: p, q, m, N of Eq. (17) (undefined while n/log³ n < 1) → pN n = 2^{⌊log₂ ⌊n/ln³ n⌋⌋}, qN n = least prime > 2√p, mN n = log₂ p + 1, QN n = q^{⌊n/m⌋}, NN n = Q p⁴; statements for n ≥ n₀; reason: Eq. (17) literally; for small n the values are placeholders and n₀ is quantified with the other constants
--   - generalization: m = log₂ p + 1 is assumed to divide n, and H_j is the j-th block of n/m coordinates (p. 16) → every n ≥ n₀, with footnote 7's blocks: blocks 1, …, m−1 of ℓ = ⌊n/m⌋ coordinates and block m of the remaining n − (m−1)ℓ; Q = q^ℓ; reason: footnote 7 gives this decomposition for all n; when m | n it is exactly the main text's, so the Lean statement specializes to the printed one
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 23 (PDF 25), Lemma 4.9

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics
import Definitions.Def_CosetTreeSVP_SVP_Tree

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_4_9 (t : ℝ) (ht0 : t0 < t) (ht1 : t < 1 / 4) :
    ∃ c : ℝ, 0 < c ∧ ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 →
      ∀ d : ℝ, SuperlatSVP.lam1 (SuperlatSVP.lat B) ≤ d →
        d ≤ (1 + 1 / (n : ℝ)) * SuperlatSVP.lam1 (SuperlatSVP.lat B) →
        prU {U : Matrix.GeneralLinearGroup (Fin n) (ZMod (qN n)) |
            ¬ ∀ j < mN n,
              SuperlatSVP.rhoSet (sigmaJ (qN n) (sPar n t d) j) (Kj (mN n) B U j \ {0}) ≤
                  ENNReal.ofReal ((2 : ℝ) ^ (-(gPar t / 2 - ε n) * n)) ∧
                SuperlatSVP.rhoSet (sigmaJ (qN n) (sPar n t d) j / Real.sqrt (1 - 1 / (n : ℝ)))
                    (Kj (mN n) B U j \ {0}) ≤
                  ENNReal.ofReal ((2 : ℝ) ^ (-(gPar t / 2 - ε n) * n))} ≤
          ENNReal.ofReal ((2 : ℝ) ^ (-(c * n))) := by sorry

end CosetTreeSVP.SVP
