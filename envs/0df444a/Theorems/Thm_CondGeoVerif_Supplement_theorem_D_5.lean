-- Prove2me | Theorems.Thm_CondGeoVerif_Supplement_theorem_D_5
-- name    : CondGeoVerif.Supplement.theorem_D_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T02:16:08.016241+00:00
-- url     : https://prove2.me/theorems/04cfa579-6dd1-444a-967c-9ed278c4ad6d
-- title:
--   Theorem D.5 — Gaussian baseline $\mathbb EH_\lambda\le-g_a\theta$ and risk certificate $R(h_0)-R(h_w)\le-g_a\theta+2A_\lambda+2\|V_\lambda\|$
-- statement:
--   Let $\eta^\dagger$ be the threshold of Theorem D.2, $a^\dagger=1-2\eta^\dagger$, fix $a\in(a^\dagger,1)$ and $\eta=(1-a)/2$. Let $X\sim N(0,I_d)$, $v$ a unit candidate normal, $S\in\mathbb R^{d\times m}$ with orthonormal columns perpendicular to $v$, $T=v\cdot X$, $U=S^\top X$, $Z=(I-vv^\top-SS^\top)X$, $\lambda=(c,\beta,\sigma)$ a unit coefficient tuple with $\sigma\ge0$, $n$ a residual unit direction when $\sigma>0$, $h_0=\mathrm{sign}(T)$, $h_w=\mathrm{sign}(cT+\beta\cdot U+\sigma n\cdot X)$ and $\theta=\arccos c$. With $H_\lambda$, $\alpha_\lambda,\gamma_\lambda$, $A_\lambda$, $V_\lambda$ as in §D.4 (for $\sigma=0$: $\alpha_\lambda=D_\lambda$, $\gamma_\lambda=0$, $H_\lambda=-aD_\lambda$), there is $g_a>0$ (Lemma D.4) such that, for every dimension, candidate, revealed frame, coefficient tuple and residual direction,
--   $$\mathbb EH_\lambda\le-g_a\theta\quad\text{for every }\theta\in[0,\pi],\qquad(D.11)$$
--   and for every stochastic labeling, with $E_0=1\{Y\ne h_0(X)\}$, $A_\lambda=\mathbb E[\alpha_\lambda(E_0-\eta)]$, $V_\lambda=\mathbb E[\gamma_\lambda\,\mathrm{sign}(T)ZE_0]$,
--   $$R(h_0)-R(h_w)\le-g_a\theta+2A_\lambda+2\|V_\lambda\|.\qquad(D.12)$$
--   The signed coefficients obey the pointwise dual inequality (D.3): $e\,1\{x<-u\}\le(1\{x<-u\}-\alpha_\eta(u)-\gamma_\eta(u)x)_++\alpha_\eta(u)e+\gamma_\eta(u)xe$ for all real $x,u$ and $e\in[0,1]$; the value identity (D.4): $M_\eta(u)=\mathbb E(1\{G<-u\}-\alpha_\eta(u)-\gamma_\eta(u)G)_++\eta\alpha_\eta(u)$; and the localization bounds (D.5): $0\le\alpha_\eta\le1$, $|\gamma_\eta|\le A^{-1}$, $\{\alpha_\eta\ne0\}\subset\{u<k_\eta\}$, $\{\gamma_\eta\ne0\}\subset\{|u|<k_\eta\}$. All constants are independent of the revealed frame dimension.
--
--   Differences from the source:
--   - encoding: a† the threshold of Theorem D.2 → any η† ∈ (0, 1/2) with J_{η†} = 0, and a ∈ (1 − 2η†, 1); reason: the zero is unique by Theorem D.2
--   - encoding: g_a from Lemma D.4 → ∃ g > 0 chosen before the dimension, frame, tuple and labeling; reason: Lemma D.4 asserts existence; its explicit formula depends only on a
--   - encoding: a residual unit n when σ > 0 → n arbitrary, required to be a unit vector orthogonal to v and to the columns of S only when σ > 0; reason: for σ = 0 the residual direction is unnecessary (p.41)
--   - encoding: the roots ℓ, z of (D.2) → selected by choice where they exist; reason: Lemma D.1: they exist and are unique on −b_η < u < k_η, the only region used
-- source:
--   T. Y. Chen, The Conditional Geometry of Statistical Verification, manuscript (October 2026, STOC 2027 submission, sha256 07a66d18…), Theorem D.5, pp.41–42 (PDF pp.44–45); Lemma D.1, (D.3)–(D.5), p.38; Lemma D.4, p.41

import Mathlib
import Definitions.Def_CondGeoVerif_risk
import Definitions.Def_CondGeoVerif_Supplement_Mhalf

set_option autoImplicit false

open MeasureTheory ProjLikeRetr.Stiefel
open scoped Matrix

namespace CondGeoVerif.Supplement

open CondGeoVerif

/-- **Theorem D.5 (Gaussian baseline and risk certificate)** (Chen, *The Conditional Geometry of
Statistical Verification*, manuscript, October 2026, sha256 07a66d18…, pp.41–42 = PDF pp.44–45).
Let `η†` be the threshold of Theorem D.2, fix `a ∈ (a†, 1)`, `a† = 1 − 2η†`, and `η = (1 − a)/2`.
There is `g_a > 0` (Lemma D.4), independent of the dimension and of the revealed frame, such that
for every dimension `d`, unit candidate normal `v`, revealed frame `S ∈ ℝ^{d×m}` with orthonormal
columns perpendicular to `v`, unit coefficient tuple `λ = (c, β, σ)` with `σ ≥ 0`, and residual unit
direction `n` (perpendicular to `v` and to the columns of `S`, when `σ > 0`):
1. (D.11) `E H_λ ≤ −g_a θ`, `θ = arccos c ∈ [0, π]`, under `X ∼ N(0, I_d)`;
2. (D.12) for every stochastic labeling with feature marginal `N(0, I_d)`,
   `R(h₀) − R(h_w) ≤ −g_a θ + 2A_λ + 2‖V_λ‖`;
3. the coefficients `α_η, γ_η` satisfy the pointwise dual inequality (D.3), the value identity (D.4)
   and the localization bounds (D.5).

**Formalization Note** `η†` enters through its defining property (a zero of `J` in `(0, 1/2)`; it is
unique by Theorem D.2). `H_λ`, `α_λ`, `γ_λ`, `A_λ`, `V_λ` are `Hlam`, `alphaLam`, `gammaLam`, `Alam`,
`Vlam` (for `σ = 0`: `α_λ = D_λ`, `γ_λ = 0`, `H_λ = −aD_λ`). `g_a` is chosen before every other
quantity. `G ∼ N(0, 1)` in (D.4) is the first coordinate under `N(0, I_1)`. -/
theorem theorem_D_5 (ηd : ℝ) (hd0 : 0 < ηd) (hd1 : ηd < 1 / 2) (hJ : Jeta ηd = 0) (a : ℝ)
    (ha : 1 - 2 * ηd < a) (ha1 : a < 1) :
    ∃ g : ℝ, 0 < g ∧
      (∀ (d m : ℕ) (v : Vec d) (S : Matrix (Fin d) (Fin m) ℝ) (c : ℝ) (β : Vec m) (σ : ℝ)
          (n : Vec d),
        ‖v‖ = 1 → S ∈ stiefel d m → matVec Sᵀ v = 0 → 0 ≤ σ → c ^ 2 + ‖β‖ ^ 2 + σ ^ 2 = 1 →
        (0 < σ → ‖n‖ = 1 ∧ inner ℝ v n = 0 ∧ matVec Sᵀ n = 0) →
        (∫ x, Hlam a v S c β σ n x ∂(gauss d) ≤ -g * Real.arccos c) ∧
        ∀ P : ProbabilityMeasure (Vec d × Bool), GaussMarginal (P : Measure (Vec d × Bool)) →
          risk (P : Measure (Vec d × Bool)) (hCand v) -
              risk (P : Measure (Vec d × Bool)) (hComp v S c β σ n) ≤
            -g * Real.arccos c + 2 * Alam ((1 - a) / 2) (P : Measure (Vec d × Bool)) v S c β σ n +
              2 * ‖Vlam ((1 - a) / 2) (P : Measure (Vec d × Bool)) v S c β σ‖) ∧
      (∀ x u e : ℝ, 0 ≤ e → e ≤ 1 →
        e * ind (decide (x < -u)) ≤
          max (ind (decide (x < -u)) - alphaEta ((1 - a) / 2) u - gammaEta ((1 - a) / 2) u * x) 0 +
            alphaEta ((1 - a) / 2) u * e + gammaEta ((1 - a) / 2) u * x * e) ∧
      (∀ u : ℝ, Mhalf ((1 - a) / 2) u =
        (∫ z, max (ind (decide (z 0 < -u)) - alphaEta ((1 - a) / 2) u -
            gammaEta ((1 - a) / 2) u * z 0) 0 ∂(gauss 1)) +
          (1 - a) / 2 * alphaEta ((1 - a) / 2) u) ∧
      (∀ u : ℝ, 0 ≤ alphaEta ((1 - a) / 2) u ∧ alphaEta ((1 - a) / 2) u ≤ 1 ∧
        |gammaEta ((1 - a) / 2) u| ≤ 1 / critA ∧
        (alphaEta ((1 - a) / 2) u ≠ 0 → u < kEta ((1 - a) / 2)) ∧
        (gammaEta ((1 - a) / 2) u ≠ 0 → |u| < kEta ((1 - a) / 2))) := by sorry

end CondGeoVerif.Supplement
