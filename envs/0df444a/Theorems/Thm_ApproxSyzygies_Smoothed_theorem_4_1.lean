-- Prove2me | Theorems.Thm_ApproxSyzygies_Smoothed_theorem_4_1
-- name    : ApproxSyzygies.Smoothed.theorem_4_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:03:07.839869+00:00
-- url     : https://prove2.me/theorems/7a0cf8d7-500c-43bb-991e-9869e8e8deaf
-- title:
--   Theorem 4.1 — approximate syzygies of powers of smoothed polynomials are $n^C\rho^{-C}$-close to Koszul syzygies, w.p. $1-\exp(-\Omega(n^{\min d_i}))$
-- statement:
--   Let $\varepsilon>0$ and $d_{\max},D_{\max},T\in\mathbb N$. There are constants $C>0$, $c>0$ and a threshold $N_0$, depending only on $\varepsilon,d_{\max},D_{\max},T$, such that the following holds for every $n\ge N_0$ and every $m\ge1$. Let $d_i\in\{1,\dots,d_{\max}\}$ and $D_i\in\{1,\dots,D_{\max}\}$ ($i\in[m]$) with
--   $$\sum_{i=1}^mn^{-d_iD_i}\le n^{-\varepsilon},$$
--   let $\rho\in(0,1]$, and let $\bar a_i\in\mathbb R[x_1,\dots,x_n]_{=d_i}$ be centers of Bombieri norm at most $1$. Let $a_1,\dots,a_m$ be independent $\rho$-perturbations of the centers ($a_i=\bar a_i+\rho\sum_{|\alpha|=d_i}\zeta_{i\alpha}\sqrt{d_i!/\alpha!}\,x^\alpha$, all $\zeta_{i\alpha}$ i.i.d. $N(0,1)$) and $b_i=a_i^{D_i}$. Then, outside an event of probability at most $\exp(-c\,n^{\min_id_i})$, simultaneously for every $t\in[T]$ and every $h\in\bigoplus_{i=1}^m\mathbb R[x]_{=t-d_iD_i}$,
--   $$\mathrm{dist}\big(h,\mathcal K^{(t)}_b\big)\le n^C\rho^{-C}\Big\|\sum_{i=1}^mb_i(x)h_i(x)\Big\|,$$
--   with Bombieri norms and $\mathcal K^{(t)}_b$ the degree-$t$ Koszul syzygies of $b$ (Definition 3.2). In particular, every approximate syzygy of the powers $b_i$ is polynomially close to a Koszul syzygy, and the exact syzygy space at every degree $t\le T$ consists of the Koszul syzygies. In matrix terms, the transposed Macaulay matrix $M^{(t)}_b$ has least singular value at least $n^{-C}\rho^{C}$ on the orthogonal complement of the Koszul space.
--
--   Differences from the source:
--   - reading: "Let $m\in\mathbb N$, $\rho\in(0,1]$, $\varepsilon>0$ and $T\in\mathbb N$ be fixed ... a constant $C$ depending only on $\varepsilon,d_{\max},D_{\max},T$ ... for all sufficiently large $n$ ... $1-\exp(-\Omega(n^{\min_id_i}))$" → $\exists\,C>0,\ c>0,\ N_0$ (after $\varepsilon,d_{\max},D_{\max},T$ only), then $\forall n\ge N_0$, $\forall m\ge1$, all degrees, powers, $\rho\in(0,1]$ and centers; reason: the stronger reading: the "In particular" clause lets $m$ grow with $n$ ($m\le n^{dD-\varepsilon}$), and the proof's constants and thresholds depend only on these four parameters
--   - encoding: "with probability $1-\exp(-\Omega(n^{\min_id_i}))$, simultaneously for all $t\in[T]$ ... for all $h$" → the (outer) measure of the failure event $\{\exists t\in[1,T],\ \exists h:\ n^C\rho^{-C}\|\sum_ib_ih_i\|<\mathrm{dist}(h,\mathcal K^{(t)}_b)\}$ is at most $\exp(-c\,n^{\min_id_i})$; reason: one event for all $t$ and $h$; the failure-set form avoids measurability questions
--   - encoding: independent $\rho$-perturbed polynomials $a_i$ with centers $\bar a_i$ → `perturb (abar i) ρ (ω i)` under `gaussCoeffs n m d` (i.i.d. $N(0,1)$ for every $i$ and every $|\alpha|=d_i$, Bombieri-normalised monomials); reason: the definition on p. 17
--   - encoding: $m\in\mathbb N$ → $m\ge1$ (`[NeZero m]`); reason: $\min_id_i$ needs $m\ge1$; for $m=0$ there is nothing to prove
--   - encoding: "In particular, if $d_i=d$ and $D_i=D$ for all $i$, then this holds whenever $m\le n^{dD-\varepsilon}$" → not a separate clause; reason: for equal degrees the slack hypothesis reads $mn^{-dD}\le n^{-\varepsilon}$, i.e. $m\le n^{dD-\varepsilon}$, so this is the instance of the stated theorem with the same constants
--   - encoding: $d_i=\deg a_i\in[d_{\max}]$ → $a_i$ lives in $\mathbb R[x]_{=d_i}$ with $1\le d_i\le d_{\max}$ given; reason: a $\rho$-perturbed polynomial of degree $d_i$ is drawn in $\mathbb R[x]_{=d_i}$
--   - encoding: $\mathbb R[x]_{=d}$ with the Bombieri inner product; $\mathbb R[x]_{=d}=\{0\}$ for $d<0$ → `Hom σ d` = Euclidean space on the multi-indices $|\alpha|=d$ (empty for $d<0$), read as $\sum_\alpha p_\alpha\sqrt{d!/\alpha!}\,x^\alpha$ by `toPoly`; `ofPoly d f` reads a polynomial back; integer degrees; reason: the Bombieri-orthonormal coordinates make the Bombieri norm the Euclidean norm (p. 17); integer degrees give the zero space for negative degree with no truncated subtraction
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), p. 19, Theorem 4.1 (informal version: Theorem 1.1, p. 4)

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Bombieri

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed

/-- Theorem 4.1 (p. 19): approximate syzygies of powers of smoothed polynomials are polynomially
close to Koszul syzygies, simultaneously for all output degrees `t ∈ [T]`, outside an event of
probability `exp(−c n^{min_i d_i})`; `C`, `c` and the threshold `N₀` depend only on
`ε, d_max, D_max, T`. -/
theorem theorem_4_1 (ε : ℝ) (hε : 0 < ε) (dmax Dmax T : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ c : ℝ, 0 < c ∧ ∃ N₀ : ℕ,
      ∀ n : ℕ, N₀ ≤ n → ∀ (m : ℕ) [NeZero m] (d D : Fin m → ℕ),
        (∀ i, 1 ≤ d i ∧ d i ≤ dmax) → (∀ i, 1 ≤ D i ∧ D i ≤ Dmax) →
        ∑ i, (n : ℝ) ^ (-((d i * D i : ℕ) : ℝ)) ≤ (n : ℝ) ^ (-ε) →
        ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 →
        ∀ abar : ∀ i, Hom (Fin n) (d i : ℤ), (∀ i, ‖abar i‖ ≤ 1) →
          gaussCoeffs n m (fun i => (d i : ℤ))
            {ω | ∃ t : ℕ, 1 ≤ t ∧ t ≤ T ∧
              ∃ h : Tup (Fin n) (fun i => (t : ℤ) - ((d i : ℤ) * (D i : ℕ))),
                (n : ℝ) ^ C * ρ ^ (-C) *
                    ‖mulMap (fun i => powHom (perturb (abar i) ρ (ω i)) (D i)) (t : ℤ) h‖ <
                  Metric.infDist h
                    (koszul (fun i => powHom (perturb (abar i) ρ (ω i)) (D i)) (t : ℤ))}
            ≤ ENNReal.ofReal
                (Real.exp (-(c * (n : ℝ) ^ (Finset.univ.inf' Finset.univ_nonempty d)))) := by sorry

end ApproxSyzygies.Smoothed
