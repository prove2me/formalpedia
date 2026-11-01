-- Prove2me | Theorems.Thm_EthierKurtz_steered_euler_coupling_tracking
-- name    : EthierKurtz.steered_euler_coupling_tracking
-- status  : Proved
-- author  : @Nickrobbins95
-- created : 2026-10-31T18:07:18.314886+00:00
-- url     : https://prove2.me/theorems/f5179c30-a393-4c35-be34-a40a085da528
-- title:
--   Tracking estimate for the steered Euler coupling of a Brownian SDE: the difference follows the linear interpolation to zero
-- statement:
--   Let $W$ be a standard $d$-dimensional Brownian motion, $0<h\le 1$, and let $s_1,b_1$ be continuous coefficients bounded by $S$ and $L$-Lipschitz. Let $J(p,\cdot)$ be a jointly measurable right inverse of the averaged diffusion $v\mapsto \tfrac12(s_1(p_1)+s_1(p_2))v$. On the cells $[lh,(l+1)h]$ put $\xi_l=W_{(l+1)h}-W_{lh}$ and $\zeta_l=\frac1h\int_0^h (W_{(l+1)h}-W_{lh+u})\,du$, and let $Z(p;a,c)=p_2+\sum_j\big(s_1(p_1)_{\cdot j}a_j+(s_1(p_2)-s_1(p_1))_{\cdot j}c_j\big)+\tfrac h2(b_1(p_1)+b_1(p_2))$ be the two-step (Heun-type) scheme in noise form. Run the coupled chain $Q_k=((X_{k-1},X_k),(\hat Y_{k-1},\hat Y_k))$ from $Q_0=q_0$, where $X$ uses the noises $(\xi_k,\zeta_k)$ and $\hat Y$ the steered noises $(\xi_k+U_k,\zeta_k+U_k/2)$ with steering drift $U_k=J(\hat Y\text{-pair},(X_k-\hat Y_k)/(m-k))$ for $k<m$ and $0$ afterwards. If $m\ge 2$, $\delta>0$, and both initial differences satisfy $|\cdot|^2\le G$, then with $T=mh$, $D_k=X_k-\hat Y_k$, $$P\Big(\exists k\le m-1:\ \big|D_k-\tfrac{m-k}{m}D_0\big|\ge\delta\Big)\le \frac{4G\,(1+13(1+13ch)^m)\,(12dL^2T+L^2T^2)}{\delta^2},\qquad c=2L+L^2+6dL^2.$$
-- source:
--   A. Hening, D. H. Nguyen, Coexistence and extinction for stochastic Kolmogorov systems, arXiv:1704.06984v1, https://arxiv.org/abs/1704.06984, proof of Lemma 3.6 in the Appendix (p. 32: overlap of transition probabilities of a nondegenerate diffusion started in a compact set); the steering (control) coupling and its tracking estimate follow the Girsanov coupling of M. Hairer, J. C. Mattingly, M. Scheutzow, Asymptotic coupling and a general form of Harris' theorem with applications to stochastic delay equations, Probab. Theory Related Fields 149 (2011) 223-259, https://doi.org/10.1007/s00440-009-0250-6, Section 2; discrete-time version via Doob's L2 maximal inequality for the martingale part and a discrete Gronwall bound.

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_EthierKurtz_IsStandardBrownian
import Definitions.Def_EthierKurtz_SDEDiffusion
open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology BigOperators

namespace EthierKurtz

theorem steered_euler_coupling_tracking {Ω : Type*} [MeasurableSpace Ω] {d : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {W : ℝ≥0 → Ω → SDEState d} (hW : IsStandardBrownian P W)
    {h : ℝ≥0} (hh : 0 < (h : ℝ)) (hh1 : (h : ℝ) ≤ 1)
    {s₁ : SDEState d → SDEDiffusion d} {b₁ : SDEState d → SDEState d}
    (hs : Continuous s₁) (hb : Continuous b₁)
    {J : SDEState d × SDEState d → SDEState d → (Fin d → ℝ)} (hJm : Measurable (Function.uncurry J))
    (hJ : ∀ p v, WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) + s₁ p.2 (i, j)) / 2 * J p v j) = v)
    {S L : ℝ} (hL : 0 ≤ L) (hSg : ∀ x, ‖s₁ x‖ ≤ S ∧ ‖b₁ x‖ ≤ S)
    (hLg : ∀ x y, ‖s₁ x - s₁ y‖ ≤ L * ‖x - y‖ ∧ ‖b₁ x - b₁ y‖ ≤ L * ‖x - y‖)
    {m : ℕ} (hm2 : 2 ≤ m) (ξ ζ : ℕ → Ω → Fin d → ℝ)
    (hξ : ∀ l ω j, ξ l ω j = W (((l : ℝ) * h).toNNReal + h) ω j - W ((l : ℝ) * h).toNNReal ω j)
    (hζ : ∀ l ω j, ζ l ω j = (1 / (h : ℝ)) * ∫ u in (0 : ℝ)..h,
      (W (((l : ℝ) * h).toNNReal + h) ω j - W (((l : ℝ) * h).toNNReal + u.toNNReal) ω j))
    (Z : SDEState d × SDEState d → (Fin d → ℝ) → (Fin d → ℝ) → SDEState d)
    (hZ : ∀ p a c, Z p a c = p.2 + WithLp.toLp 2 (fun i => ∑ j, (s₁ p.1 (i, j) * a j +
      (s₁ p.2 (i, j) - s₁ p.1 (i, j)) * c j) + (h : ℝ) / 2 * (b₁ p.1 i + b₁ p.2 i)))
    (Q : ℕ → Ω → (SDEState d × SDEState d) × (SDEState d × SDEState d))
    (q₀ : (SDEState d × SDEState d) × (SDEState d × SDEState d)) (hQ0 : ∀ ω, Q 0 ω = q₀)
    (U : ℕ → Ω → Fin d → ℝ)
    (hU : ∀ k ω, U k ω = if k < m then
      J (Q k ω).2 ((1 / ((m : ℝ) - k)) • ((Q k ω).1.2 - (Q k ω).2.2)) else 0)
    (hQ : ∀ k ω, Q (k + 1) ω = (((Q k ω).1.2, Z (Q k ω).1 (ξ k ω) (ζ k ω)),
      ((Q k ω).2.2, Z (Q k ω).2 (ξ k ω + U k ω) (ζ k ω + fun j => U k ω j / 2))))
    {δ : ℝ} (hδ : 0 < δ) {G : ℝ}
    (hG1 : ‖q₀.1.1 - q₀.2.1‖ ^ 2 ≤ G) (hG2 : ‖q₀.1.2 - q₀.2.2‖ ^ 2 ≤ G) :
    P.real {ω | ∃ k ≤ m - 1, δ ≤ ‖((Q k ω).1.2 - (Q k ω).2.2) -
        (((m : ℝ) - k) / m) • ((Q 0 ω).1.2 - (Q 0 ω).2.2)‖} ≤
      4 * G * (1 + 13 * (1 + 13 * (2 * L + L ^ 2 + 6 * d * L ^ 2) * h) ^ m) *
        (12 * d * L ^ 2 * ((m : ℝ) * h) + L ^ 2 * ((m : ℝ) * h) ^ 2) / δ ^ 2 := by sorry

end EthierKurtz
