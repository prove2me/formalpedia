-- Prove2me | Theorems.Thm_EthierKurtz_steered_euler_coupling_lower_box
-- name    : EthierKurtz.steered_euler_coupling_lower_box
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T18:08:23.583517+00:00
-- url     : https://prove2.me/theorems/7079ec48-5492-4813-8bc5-3d9a04db7404
-- title:
--   Finite-step minorisation for the steered Euler coupling of a Brownian SDE
-- statement:
--   Setting as in the tracking estimate for the steered Euler coupling: $W$ a standard $d$-dimensional Brownian motion, $0<h\le1$, continuous coefficients $s_1,b_1$ bounded by $S$ and $L$-Lipschitz, $J(p,\cdot)$ a jointly measurable right inverse of the averaged diffusion with $\sum_j J(p,v)_j^2\le\Lambda^2|v|^2$, cell noises $\xi_l,\zeta_l$ and the Heun-type two-step map $Z$. Let $Y_p$ be the uncoupled two-step chain started at the pair $p$ (driven by $(\xi_k,\zeta_k)$). Let $m\ge2$, $q_0=(p_1,p_2)$ with both initial differences of squared norm $\le G$, $0<\varepsilon\le\delta$, $a>0$, $m h S\le\delta/2$, $A,B_x$ measurable, $B$ with $\varepsilon$-neighbourhood inside $A$, and $B_x$ containing the $2\delta$-tube around the segment from $p_{1,2}$ to $p_{2,2}$. Then
--
--   $$e^{-a}\Big(P\big((Y_{p_1})_m\in B\big)-\frac{16dS^2mh}{(\delta/2)^2}-E_{\rm track}-\frac{5chG(1+13ch)^m}{m^2\varepsilon^2}-\frac{\Lambda^2G(1+13ch)^m/(2mh)+1}{a}\Big)\le P\big((Y_{p_2})_m\in A,\ (Y_{p_2})_k\in B_x\ \forall k\le m\big),$$
--
--   with $c=2L+L^2+6dL^2$ and $E_{\rm track}$ the bound of the tracking estimate. Role: the finite-step minorisation of the second chain by the first one (steering coupling plus a Gaussian change of measure with relative entropy bounded via $\Lambda$), the discrete core of the local total-variation overlap.
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Lemma 3.6 in the Appendix (p. 32: overlap of transition probabilities of a nondegenerate diffusion started in a compact set); the steering (control) coupling and its tracking estimate follow the Girsanov coupling of M. Hairer, J. C. Mattingly, M. Scheutzow, Asymptotic coupling and a general form of Harris' theorem with applications to stochastic delay equations, Probab. Theory Related Fields 149 (2011) 223-259, https://doi.org/10.1007/s00440-009-0250-6, Section 2; discrete-time version via Doob's L2 maximal inequality for the martingale part and a discrete Gronwall bound.

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem steered_euler_coupling_lower_box {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {h : ℝ≥0} (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    (hs : Continuous s₁) (hb : Continuous b₁)
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} (hJm : Measurable (Function.uncurry J))
    (hJ : ∀ p v, WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) + s₁ p.2 (i, j)) / 2 * J p v j) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {Λ : ℝ} (hΛ : ∀ p v, ∑ j, J p v j ^ 2 ≤ Λ ^ 2 * ‖v‖ ^ 2)
    {m : ℕ} (hm2 : 2 ≤ m) (ξ ζ : ℕ → Ω → Fin d → ℝ)
    (hξ : ∀ l ω j, ξ l ω j = W (((l : ℝ) * h).toNNReal + h) ω j - W ((l : ℝ) * h).toNNReal ω j)
    (hζ : ∀ l ω j, ζ l ω j = (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h,
      (W (((l : ℝ) * h).toNNReal + h) ω j - W (((l : ℝ) * h).toNNReal + u.toNNReal) ω j))
    (Z : SDEState d × SDEState d → (Fin d → ℝ) → (Fin d → ℝ) → SDEState d)
    (hZ : ∀ p a c, Z p a c = p.2 + WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) * a j +
      (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * c j) + (h : ℝ) / 2 * (b₁ p.1 i + b₁ p.2 i)))
    (Y : SDEState d × SDEState d → ℕ → Ω → SDEState d × SDEState d)
    (hY0 : ∀ p ω, Y p 0 ω = p) (hY : ∀ p k ω, Y p (k + 1) ω = ((Y p k ω).2, Z (Y p k ω) (ξ k ω) (ζ k ω)))
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) {G : ℝ}
    (hG1 : ‖q₀.1.1 - q₀.2.1‖ ^ 2 ≤ G) (hG2 : ‖q₀.1.2 - q₀.2.2‖ ^ 2 ≤ G)
    {δ ε a : ℝ} (hδ : 0 < δ) (hε : 0 < ε) (hεδ : ε ≤ δ) (ha : 0 < a)
    (hT : m * (h * S) ≤ δ / 2)
    {A B Bx : Set (SDEState d)} (hA : MeasurableSet A) (hBxm : MeasurableSet Bx)
    (hB : ∀ z ∈ B, ∀ z', ‖z' - z‖ < ε → z' ∈ A)
    (hBx : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → ∀ z,
      ‖z - (q₀.1.2 - t • (q₀.1.2 - q₀.2.2))‖ < 2 * δ → z ∈ Bx) :
    Real.exp (-a) * (P.real {ω | (Y q₀.1 m ω).2 ∈ B} -
        16 * d * S ^ 2 * (m * h) / (δ / 2) ^ 2 -
        4 * G * (1 + 13 * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m) *
          (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) / δ ^ 2 -
        5 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h * G *
          (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / (m : ℝ) ^ 2 / ε ^ 2 -
        (Λ ^ 2 * (G * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m / m) / (2 * h) + 1) / a) ≤
      P.real {ω | (Y q₀.2 m ω).2 ∈ A ∧ ∀ k ≤ m, (Y q₀.2 k ω).2 ∈ Bx} := by sorry

end EthierKurtz
