-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_3_4
-- name    : CosetTreeSVP.SVP.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:32:35.472282+00:00
-- url     : https://prove2.me/theorems/abd071b9-0d5e-47a8-a2fa-75b4a43aa481
-- title:
--   Lemma 3.4 — for an odd prime q and w = B⁻¹v mod q: f(w) = 2^{−4tnλ²/(d²q²)}(1 + O(2^{−Ω(n)})) and ‖−G(w)/f(w) − 2πs²v/q‖ ≤ 2^{−Ω(n)}s²λ
-- statement:
--   Let $L = B\mathbb Z^n$ for a nonsingular $B \in \mathbb R^{n\times n}$, $\lambda = \lambda_1(L)$, and let $s = \sqrt{4nt\ln 2/(\pi d^2)}$, $g = \tfrac12\log_2(t/t_0)$ with $t_0 = \beta^2/(4e\ln 2)$.
--
--   **Lemma 3.4.** Fix $t_0 < t < 1/4$. There are constants $C$, $c > 0$ and $n_0$ such that for all $n \ge n_0$, every odd prime $q$, every nonsingular $B$, every $d$ with $\lambda \le d \le (1+1/n)\lambda$, every shortest vector $v$ of $L$ and $w = B^{-1}v \bmod q$:
--   $$f(w) = 2^{-4tn\lambda^2/(d^2q^2)}(1+\eta)\ \text{ for some } |\eta| \le C2^{-cn},\qquad \Big\|-\frac{G(w)}{f(w)} - \frac{2\pi s^2v}{q}\Big\| \le 2^{-cn}s^2\lambda.$$
--   The gradient of the periodic Gaussian at $v/q$ points along $v$: this is the main idea of the algorithm.
--
--   Differences from the source:
--   - encoding: O(2^{−Ω(n)}) and 2^{−Ω(n)}, uniform over q → constants C, c > 0 and n₀ chosen after t and before n, q, B, d, v; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - reading: β = 2^{0.4014...}, the lattice-point constant of [KL78] and [PS09, Lemma 3]; t0 = β²/(4e ln 2) = 0.23147… → beta = 2^R with R = a log₂ a − b log₂ b, a = (1 + sin(π/3))/(2 sin(π/3)), b = (1 − sin(π/3))/(2 sin(π/3)); t0 = beta²/(4e ln 2); reason: the printed decimals pin the Kabatiansky–Levenshtein exponent at angle π/3: R = 0.401413…, t0 = 0.231470…, 1/(2√t0) = 1.039255…, all matching the paper
--   - encoding: f(w) = F_{1/s}(Bw/q), G(w) = ∇F_{1/s}(Bw/q) (Eqs. (9)–(11)) → fq, Gq by the primal series of Eqs. (9), (10) at Bw/q, w lifted to {0, …, q−1}ⁿ; reason: the paper's own first representations; periodicity makes the value independent of the lift, and the series is the termwise derivative
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 13 (PDF 15), Lemma 3.4

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_3_4 (t : ℝ) (ht0 : t0 < t) (ht1 : t < 1 / 4) :
    ∃ C c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ q : ℕ, q.Prime → q ≠ 2 →
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 →
      ∀ d : ℝ, SuperlatSVP.lam1 (SuperlatSVP.lat B) ≤ d →
        d ≤ (1 + 1 / (n : ℝ)) * SuperlatSVP.lam1 (SuperlatSVP.lat B) →
      ∀ v : E n, IsShortestVec (SuperlatSVP.lat B) v →
        (∃ η : ℝ, |η| ≤ C * (2 : ℝ) ^ (-(c * n)) ∧
          fq B q (sPar n t d) (coeffMod B q v) =
            (2 : ℝ) ^ (-(4 * t * n * SuperlatSVP.lam1 (SuperlatSVP.lat B) ^ 2 /
              (d ^ 2 * (q : ℝ) ^ 2))) * (1 + η)) ∧
        ‖-((fq B q (sPar n t d) (coeffMod B q v))⁻¹ • Gq B q (sPar n t d) (coeffMod B q v)) -
            (2 * Real.pi * sPar n t d ^ 2 / q) • v‖ ≤
          (2 : ℝ) ^ (-(c * n)) * sPar n t d ^ 2 * SuperlatSVP.lam1 (SuperlatSVP.lat B) := by sorry

end CosetTreeSVP.SVP
