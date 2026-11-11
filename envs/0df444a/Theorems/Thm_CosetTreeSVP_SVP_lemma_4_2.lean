-- Prove2me | Theorems.Thm_CosetTreeSVP_SVP_lemma_4_2
-- name    : CosetTreeSVP.SVP.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:32:29.363358+00:00
-- url     : https://prove2.me/theorems/c5b88cd6-9e30-4d21-b8f2-79ccaa21dda3
-- title:
--   Lemma 4.2 — an A ∈ ℂⁿ within (s²λ/q)2^{−n/4+o(n)} of cG(w)f(w)^{p−1}, |c| = 1, gives from Re A or Im A a unit vector u with ‖±du − v‖ < 2λ/n
-- statement:
--   Let $L = B\mathbb Z^n$ for a nonsingular $B \in \mathbb R^{n\times n}$, $\lambda = \lambda_1(L)$, and let $s = \sqrt{4nt\ln 2/(\pi d^2)}$, $g = \tfrac12\log_2(t/t_0)$ with $t_0 = \beta^2/(4e\ln 2)$. Let $p, q$ be the parameters of Eq. (17).
--
--   **Lemma 4.2.** Fix $t_0 < t < 1/4$ and a function $h$ with $h(n)/n \to 0$. There are $c > 0$ and $n_0$ such that for all $n \ge n_0$, every nonsingular $B$, every $d$ with $\lambda \le d \le (1+1/n)\lambda$, every shortest vector $v$, $w = B^{-1}v \bmod q$: if $A \in \mathbb C^n$ and $|\gamma| = 1$ satisfy
--   $$\big\|A - \gamma\,G(w)f(w)^{p-1}\big\| \le \frac{s^2\lambda}{q}\,2^{-n/4+h(n)},\tag{18}$$
--   then for $u = \operatorname{Re}A/\|\operatorname{Re}A\|$ (with $\operatorname{Re}A \ne 0$) or $u = \operatorname{Im}A/\|\operatorname{Im}A\|$ (with $\operatorname{Im}A \ne 0$) and a sign $\sigma \in \{\pm1\}$,
--   $$\|u - \sigma v/\lambda\| \le 2^{-cn}\quad\text{and}\quad\|\sigma du - v\| < 2\lambda/n.$$
--   It reduces the search to approximating $G(w)f(w)^{p-1}$ up to a unit factor.
--
--   Differences from the source:
--   - encoding: o(n) in the hypothesis (18), 2^{−Ω(n)} in the conclusion, 'for all sufficiently large n' → ∀ h with h(n)/n → 0, ∃ c > 0, ∃ n₀, for every n ≥ n₀ and every B, d, v, A, γ; reason: the paper's convention (p. 11): n tends to infinity and every o, O, Ω is uniform over the parameters; the functions and constants are chosen after the fixed t and before n, the basis, d and v
--   - reading: 'one of the well-defined nonzero vectors ReA/‖ReA‖ and ImA/‖ImA‖ is within 2^{−Ω(n)} of either v/λ or −v/λ; for the corresponding unit vector u, ‖±du − v‖ < 2λ/n for all sufficiently large n' → ∃ u (Re A ≠ 0 and u = ReA/‖ReA‖, or Im A ≠ 0 and u = ImA/‖ImA‖), ∃ σ ∈ {1, −1}: ‖u − σv/λ‖ ≤ 2^{−cn} and ‖σdu − v‖ < 2λ/n, for n ≥ n₀; reason: the sign ± of the second claim is the one of the first (the proof's sgn(Re c)); nonvanishing (footnote 6) is part of the conclusion; the whole lemma is asymptotic
--   - reading: β = 2^{0.4014...}, the lattice-point constant of [KL78] and [PS09, Lemma 3]; t0 = β²/(4e ln 2) = 0.23147… → beta = 2^R with R = a log₂ a − b log₂ b, a = (1 + sin(π/3))/(2 sin(π/3)), b = (1 − sin(π/3))/(2 sin(π/3)); t0 = beta²/(4e ln 2); reason: the printed decimals pin the Kabatiansky–Levenshtein exponent at angle π/3: R = 0.401413…, t0 = 0.231470…, 1/(2√t0) = 1.039255…, all matching the paper
--   - encoding: p, q, m, N of Eq. (17) (undefined while n/log³ n < 1) → pN n = 2^{⌊log₂ ⌊n/ln³ n⌋⌋}, qN n = least prime > 2√p, mN n = log₂ p + 1, QN n = q^{⌊n/m⌋}, NN n = Q p⁴; statements for n ≥ n₀; reason: Eq. (17) literally; for small n the values are placeholders and n₀ is quantified with the other constants
--   - encoding: f(w) = F_{1/s}(Bw/q), G(w) = ∇F_{1/s}(Bw/q) (Eqs. (9)–(11)) → fq, Gq by the primal series of Eqs. (9), (10) at Bw/q, w lifted to {0, …, q−1}ⁿ; reason: the paper's own first representations; periodicity makes the value independent of the lift, and the series is the termwise derivative
-- source:
--   Hhan, Finding a Shortest Vector and More in 2^{n/2+o(n)} Time using q-ary Coset Difference Tree, arXiv:2609.02764 (held version, sha256 687602f4…), p. 15 (PDF 17), Lemma 4.2

import Mathlib
import Definitions.Def_SuperlatSVP_lat
import Definitions.Def_RegevLWE_GaussConv_Lattice
import Definitions.Def_RegevLWE_Hyperplane_DiscreteGaussian
import Definitions.Def_CosetTreeSVP_SVP_Basics

open MeasureTheory Filter Topology
open scoped ENNReal

namespace CosetTreeSVP.SVP

theorem lemma_4_2 (t : ℝ) (ht0 : t0 < t) (ht1 : t < 1 / 4) (h : ℕ → ℝ)
    (hh : Tendsto (fun n => h n / n) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n ≥ n₀,
      ∀ B : Matrix (Fin n) (Fin n) ℝ, B.det ≠ 0 →
      ∀ d : ℝ, SuperlatSVP.lam1 (SuperlatSVP.lat B) ≤ d →
        d ≤ (1 + 1 / (n : ℝ)) * SuperlatSVP.lam1 (SuperlatSVP.lat B) →
      ∀ v : E n, IsShortestVec (SuperlatSVP.lat B) v →
      ∀ (A : CE n) (γ : ℂ), ‖γ‖ = 1 →
        ‖A - (γ * ((fq B (qN n) (sPar n t d) (coeffMod B (qN n) v) ^ (pN n - 1) : ℝ) : ℂ)) •
            toC (Gq B (qN n) (sPar n t d) (coeffMod B (qN n) v))‖ ≤
          sPar n t d ^ 2 * SuperlatSVP.lam1 (SuperlatSVP.lat B) / (qN n : ℝ) *
            (2 : ℝ) ^ (-((n : ℝ) / 4) + h n) →
        ∃ u : E n,
          ((reVec A ≠ 0 ∧ u = ‖reVec A‖⁻¹ • reVec A) ∨
            (imVec A ≠ 0 ∧ u = ‖imVec A‖⁻¹ • imVec A)) ∧
          ∃ σ : ℝ, (σ = 1 ∨ σ = -1) ∧
            ‖u - σ • ((SuperlatSVP.lam1 (SuperlatSVP.lat B))⁻¹ • v)‖ ≤ (2 : ℝ) ^ (-(c * n)) ∧
            ‖(σ * d) • u - v‖ < 2 * SuperlatSVP.lam1 (SuperlatSVP.lat B) / n := by sorry

end CosetTreeSVP.SVP
