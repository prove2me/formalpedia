-- Prove2me | Theorems.Thm_EthierKurtz_euler_chain_steer_minorisation
-- name    : EthierKurtz.euler_chain_steer_minorisation
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-11-03T20:08:18.123017+00:00
-- url     : https://prove2.me/theorems/db9b5374-5cb2-4fa4-b08d-5bf9b12f491c
-- title:
--   Minorisation of two-step Euler chains by steering one start point to another
-- statement:
--   Let $W$ be a standard $d$-dimensional Brownian motion, $h\in(0,1]$, and let $Z^u$ be the two-step Euler chain of the coefficients $s_1,b_1$ started at $(u,u)$ (cell increments $\xi_k$ and cell averages $\zeta_k$ of $W$). Suppose $s_1,b_1$ agree on a set $N$ with continuous coefficients $s_2,b_2$ that are bounded by $S$, $L$-Lipschitz and whose averaged diffusion matrix has a measurable right inverse $J$ with $|J(p,v)|\le\Lambda|v|$. If every point within $2\delta$ of the segment $[x,y]$ lies in a measurable $B_x\subseteq N$, $|x-y|^2\le G$, $m\ge2$, $mhS\le\delta/2$, $0<\varepsilon\le\delta$, $a>0$, and the $\varepsilon$-neighbourhood of $B$ lies in the measurable set $A$, then
--
--   $$e^{-a}\Big(\mathbb P(Z^x_m\in B)-\frac{32dS^2mh}{(\delta/2)^2}-\frac{4G(1+13E)(12dL^2mh+L^2(mh)^2)}{\delta^2}-\frac{5chGE}{m^2\varepsilon^2}-\frac{\Lambda^2GE/(2mh)+1}{a}\Big)\le\mathbb P(Z^y_m\in A),$$
--
--   where $c=2L+L^2+6dL^2$ and $E=(1+13ch)^m$.
--
--   Role: the finite-$h$ minorisation that, after $h\to0$ (Euler convergence), shows that a box of the open orthant reaches every ball with positive probability in a short time window, the irreducibility input of the extinction theorem.
--
--   **Formalization Note**: the chains are given through their recursion (hypotheses hZ0, hZs), with the cell average written as an interval integral of $W$.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, https://arxiv.org/abs/1704.06984, proof of Theorem 5.1, p. 24 (the irreducibility step after (5.15): a process started in a compact box of the open orthant reaches every ball with positive probability); the steered (controlled) Euler chain follows the control argument for minorization of time discretizations in J. C. Mattingly, A. M. Stuart, D. J. Higham, Ergodicity for SDEs and approximations: locally Lipschitz vector fields and degenerate noise, Stochastic Process. Appl. 101 (2002) 185-232, https://doi.org/10.1016/S0304-4149(02)00150-3

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem euler_chain_steer_minorisation {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {d : ℕ} {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {h : ℝ≥0} (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    {s₁ s₂ : SDEState d → SDEDiffusion d} {b₁ b₂ : SDEState d → SDEState d}
    (hs : Continuous s₂) (hb : Continuous b₂)
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)}
    (hJm : Measurable (Function.uncurry J))
    (hJ : ∀ p v, (WithLp.toLp 2 (fun i => ∑ j, (s₂ p.1 (i, j) + s₂ p.2 (i, j)) / 2 * J p v j) :
      SDEState d) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₂ x‖ ≤ S ∧ ‖b₂ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₂ x - s₂ y‖ ≤ L * ‖x - y‖ ∧ ‖b₂ x - b₂ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {N Bx : Set (SDEState d)} (hag : ∀ x ∈ N, s₁ x = s₂ x ∧ b₁ x = b₂ x) (hBxN : Bx ⊆ N)
    (hBxm : MeasurableSet Bx) (x y : SDEState d) {m : ℕ} (hm2 : 2 ≤ m) {G : ℝ}
    (hG : ‖x - y‖ ^ 2 ≤ G)
    {δ ε a : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ) (ha : 0 < a)
    (hT : m * (h * S) ≤ δ / 2)
    {A B : Set (SDEState d)} (hA : MeasurableSet A)
    (hB : ∀ z ∈ B, ∀ z', ‖z' - z‖ < ε → z' ∈ A)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z, ‖z - (x - t • (x - y))‖ < 2 * δ → z ∈ Bx)
    (Z : SDEState d → Ω → ℕ → SDEState d × SDEState d) (hZ0 : ∀ u ω, Z u ω 0 = (u, u))
    (hZs : ∀ u ω (k : ℕ), Z u ω (k + 1) = ((Z u ω k).2, (Z u ω k).2 + WithLp.toLp 2 (fun i =>
      ∑ j, (s₁ (Z u ω k).1 (i, j) *
          (W (((k : ℝ) * h).toNNReal + h) ω j - W ((k : ℝ) * h).toNNReal ω j) +
        (s₁ (Z u ω k).2 (i, j) - s₁ (Z u ω k).1 (i, j)) *
          ((1 / (h : ℝ)) * ∫ v in (0 : ℝ)..h,
            (W (((k : ℝ) * h).toNNReal + h) ω j - W (((k : ℝ) * h).toNNReal + v.toNNReal) ω j))) +
      (h : ℝ) / 2 * (b₁ (Z u ω k).1 i + b₁ (Z u ω k).2 i)))) :
    Real.exp (-a) * (P.real {ω | (Z x ω m).2 ∈ B} -
        2 * (16 * d * S ^ 2 * (m * h) / (δ / 2) ^ 2) -
        4 * G * (1 + 13 * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m) *
          (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) / δ ^ 2 -
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * G *
          (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / (m : ℝ) ^ 2 / ε ^ 2 -
        (Λ ^ 2 * (G * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / m) / (2 * h) + 1) / a) ≤
      P.real {ω | (Z y ω m).2 ∈ A} := by sorry

end EthierKurtz
