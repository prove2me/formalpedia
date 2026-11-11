-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_3_1
-- name    : CosetTreeSVP.SVP.lemma_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:32:28.929222+00:00
-- url     : https://prove2.me/theorems/61cef9c1-472b-4549-b8dc-16cbba68cf6f
-- title:
--   Lemma 3.1 — for λ ≤ d ≤ (1+1/n)λ: ρ_{1/s}(L) − 1 ≤ 2^{−(1/2+g−o(1))n}, ρ_{√2/s}(L) − 1 ≤ 2^{−(g−o(1))n}, and s > √2·η_{1/2}(L*)
-- statement:
--   Let $L = B\mathbb Z^n$ for a nonsingular $B \in \mathbb R^{n\times n}$, $\lambda = \lambda_1(L)$, and let $s = \sqrt{4nt\ln 2/(\pi d^2)}$, $g = \tfrac12\log_2(t/t_0)$ with $t_0 = \beta^2/(4e\ln 2)$.
--
--   **Lemma 3.1** ([Hha26, Cor. 3.2]). Fix $t_0 < t < 1/4$. There are $\varepsilon(n) \to 0$ and $n_0$ such that for all $n \ge n_0$, every nonsingular $B$ and every $d$ with $\lambda \le d \le (1+1/n)\lambda$,
--   $$\rho_{1/s}(L) - 1 \le 2^{-(1/2+g-\varepsilon(n))n},\qquad \rho_{\sqrt2/s}(L) - 1 \le 2^{-(g-\varepsilon(n))n},\qquad s > \sqrt2\,\eta_{1/2}(L^*).$$
--   Here $\eta_{1/2}(L^*)$ is the smoothing parameter: $\rho_{1/\eta}(L^{**}\setminus\{0\}) = 1/2$.
--
--   The lemma fixes the sampling width: $s$ is above the threshold of Theorem 2.2 for the dual lattice, and $f$, $G$ are close to their main terms.
--
--   **Formalization Note.** Gaussian masses are sums in $[0,\infty]$ (`SuperlatSVP.rhoSet`); $\eta$ is the published `smoothingParam` (an infimum of $\{s > 0 : \rho_{1/s}(L^{**}\setminus\{0\}) \le 1/2\}$).
--
--   Differences from the source:
--   - encoding: o(1) in the exponents; implicit 'n large' → one function ε : ℕ → ℝ with ε(n) → 0 and a threshold n₀, quantified after t and before n, B, d; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - reading: β = 2^{0.4014...}, the lattice-point constant of [KL78] and [PS09, Lemma 3]; t0 = β²/(4e ln 2) = 0.23147… → beta = 2^R with R = a log₂ a − b log₂ b, a = (1 + sin(π/3))/(2 sin(π/3)), b = (1 − sin(π/3))/(2 sin(π/3)); t0 = beta²/(4e ln 2); reason: the printed decimals pin the Kabatiansky–Levenshtein exponent at angle π/3: R = 0.401413…, t0 = 0.231470…, 1/(2√t0) = 1.039255…, all matching the paper
--   - encoding: η_ε(L*) defined by ρ_{1/η}(L** \ {0}) = ε → RegevLWE.GaussConv.smoothingParam: inf of {s > 0 : ρ_{1/s}(L** \ {0}) ≤ ε}; reason: s ↦ ρ_{1/s}(L**\{0}) is continuous and strictly decreasing from ∞ to 0 for a full-rank lattice (published RegevLWE.SmoothingLB.smoothing_remark), so the infimum is the unique solution of the equation
--   - encoding: ρ_σ(L) − 1 in ℝ → rhoSet in [0, ∞] with truncated subtraction; reason: ρ_σ(L) ≥ 1 (the term x = 0), so the truncation never acts
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 12 (PDF 14), Lemma 3.1

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_3_1 (t : ℝ) (ht0 : t0 < t) (ht1 : t < 1 / 4) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 →
      ∀ d : ℝ, SuperlatSVP.lam1 (SuperlatSVP.lat B) ≤ d →
        d ≤ (1 + 1 / (n : ℝ)) * SuperlatSVP.lam1 (SuperlatSVP.lat B) →
        SuperlatSVP.rhoSet (1 / sPar n t d) (SuperlatSVP.lat B : Set (E n)) - 1 ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-(1 / 2 + gPar t - ε n) * n)) ∧
          SuperlatSVP.rhoSet (Real.sqrt 2 / sPar n t d) (SuperlatSVP.lat B : Set (E n)) - 1 ≤
            ENNReal.ofReal ((2 : ℝ) ^ (-(gPar t - ε n) * n)) ∧
          Real.sqrt 2 * RegevLWE.GaussConv.smoothingParam (dualL (SuperlatSVP.lat B)) (1 / 2) <
            sPar n t d := by sorry

end CosetTreeSVP.SVP
