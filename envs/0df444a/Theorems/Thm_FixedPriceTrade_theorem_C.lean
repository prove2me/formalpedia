-- Prove2me | Theorems.Thm_FixedPriceTrade_theorem_C
-- name    : FixedPriceTrade.theorem_C
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:43:48.49153+00:00
-- url     : https://prove2.me/theorems/6cc12076-beda-4860-813d-dc9616a8600c
-- title:
--   Theorem C — global bound (G), $\max J_d=S(C_d)$, and the maximizing control
-- statement:
--   Let $d>0$ and let $C_d\in(1/4,1/2)$ satisfy $\tau(C_d)=d$.
--
--   1. For every measurable $h:[0,1]\to[0,1]$, set $x=(d+\int_0^1h)^{-1}$. If $x<1/d$ there is a unique $C\in(0,\bar C(d))$ with $D_C(Y_d(C))=(1+x)^{-1}$; for $x=1/d$ set $C=0$ and $P_x\equiv1/d$. Then
--   $$
--   S(C_d)-J_d(h)=\int_{\min\{C,C_d\}}^{\max\{C,C_d\}}\frac{(Y_d+U_d)|\mathcal B_d|}{(1-uY_d)^2}du+\int_0^\infty\Big[a(v')^2+\frac{e^{-2v}-1+2v}{P_x^2}-2Q_xv\Big]da\ \ge0 .
--   $$
--   2. Consequently $\max_{0\le h\le1}J_d(h)=S(C_d)$, attained by the control $h_{C_d}$ of (34).
--   3. The maximizing control is unique up to equality almost everywhere.
--   4. It has a zero arc of length $C_d$, a strictly increasing arc of length $(1-2C_d)/(1-C_d)$ and a one arc of length $C_d^2/(1-C_d)$; on the middle arc $t=C_d(1+y)$, $0\le y\le y_e(C_d)$,
--   $$
--   g(t)=d\sqrt{D_{C_d}(y)}\,e^{\mathcal I_{C_d}(y)/2},\qquad h(t)=\frac{y\,g(t)}{D_{C_d}(y)} .
--   $$
--
--   This is the variational bound behind both the welfare guarantee and the hard pairs.
--
--   Differences from the source:
--   - encoding: measurable h : [0,1] → [0,1] → measurable h : ℝ → ℝ with h(t) ∈ [0,1] for t ∈ [0,1]; reason: values outside [0,1] never enter a formula
--   - encoding: the reference curve P_x indexed by its endpoint x → refCurve d C indexed by the curvature parameter C, with endpoint x(C); C = 0 is the limiting endpoint x = 1/d, P ≡ 1/d (p.16); reason: Lemma 6.1 makes C ↦ x(C) a bijection of (0, C̄(d)) onto (0, 1/d), and p.16 sets the endpoint x = 1/d at C = 0
--   - encoding: let C be the unique solution of D_C(Y_d(C)) = (1 + x)^{−1} → an ∃! clause for x < 1/d, and (G) for every C satisfying the defining condition (or C = 0 when x = 1/d); reason: the same object; x ≤ 1/d always holds (Lemma 5.1)
--   - encoding: max_{0≤h≤1} J_d(h) = S(C_d); the maximizing control → IsGreatest of the set of values J_d(h), with witness h_{C_d} = maxControl C_d and J_d(h_{C_d}) = S(C_d); reason: max as an attained greatest element
--   - encoding: arcs and their lengths; strict increase on the middle arc → h = 0 on [0, C_d); C_d·y_e(C_d) = (1 − 2C_d)/(1 − C_d); StrictMonoOn on [C_d, C_d(1 + y_e)]; h = 1 at the join and on (C_d(1 + y_e), 1]; 1 − C_d(1 + y_e) = C_d²/(1 − C_d); reason: the arc structure of the explicit control
--   - encoding: unique up to equality almost everywhere → h =ᵐ h_{C_d} for Lebesgue measure on [0,1]; reason: Mathlib's a.e. equality
--   - encoding: the integral of (G1) in (G) → the integral of (G1) in (G), with its integrand stated integrable on (0, ∞); reason: the paper's integrands are bounded with compact support; the conjunct rules out a Bochner 0 for a non-integrable function, and adds no assumption
--   - encoding: derivatives of absolutely continuous functions (p′, (log p)′, v′) → Mathlib's deriv; reason: deriv agrees almost everywhere with the derivative of an absolutely continuous function, and the derivatives appear only under integrals or a.e. statements
-- source:
--   Lin, Shi, Dong, Li, Yu, Zhang, The Exact Welfare Guarantee of Fixed-Price Bilateral Trade, arXiv:2609.35888 (held PDF sha256 26832346…), Theorem C, p.19

import Mathlib
import Definitions.Def_FixedPriceTrade_refCurve
import Definitions.Def_FixedPriceTrade_maxControl

set_option autoImplicit false

namespace FixedPriceTrade

open MeasureTheory Set

/-- **Theorem C (global bound and maximizing control)** — Lin, Shi, Dong, Li, Yu, Zhang, *The Exact
Welfare Guarantee of Fixed-Price Bilateral Trade*, arXiv:2609.35888 (held PDF sha256 26832346…),
p.19.

Let `d > 0` and `C_d ∈ (1/4, 1/2)` with `τ(C_d) = d`.

1. For every measurable `h : [0,1] → [0,1]`, with `x = (d + ∫_0^1 h)^{−1}`: if `x < 1/d` there is
   a unique `C ∈ (0, C̄(d))` with `D_C(Y_d(C)) = (1 + x)^{−1}`; for that `C` (or `C = 0`, `P ≡ 1/d`,
   when `x = 1/d`), with `v = log(p/P_x)`, the identity (G)
   `S(C_d) − J_d(h) = ∫_{min{C,C_d}}^{max{C,C_d}} (Y_d + U_d)|B_d|/(1 − uY_d)² du
     + ∫_0^∞ [a(v′)² + (e^{−2v} − 1 + 2v)/P_x² − 2Q_x v] da ≥ 0` holds, the second integrand being
   integrable.
2. (33) `max_{0 ≤ h ≤ 1} J_d(h) = S(C_d)`, attained by the control `h_{C_d}` of (34).
3. The maximizing control is unique up to equality a.e. on `[0,1]`.
4. It has a zero arc of length `C_d`, a strictly increasing arc of length `(1 − 2C_d)/(1 − C_d)`
   and a one arc of length `C_d²/(1 − C_d)`; on the middle arc `t = C_d(1 + y)`,
   `g(t) = d √D_{C_d}(y) e^{I_{C_d}(y)/2}` and `h(t) = y g(t)/D_{C_d}(y)`, `0 ≤ y ≤ y_e(C_d)`.

**Formalization Note.** Controls are all measurable `h` with values in `[0,1]` (not only
monotone ones). `maxControl C_d` is (34) written with `g = τ(C_d) √D e^{I/2}`; the clause on `g`
says that this is the state `d + ∫_0^t h` of the control itself. -/
theorem theorem_C (d : ℝ) (hd : 0 < d) (Cd : ℝ) (hCd : Cd ∈ Ioo (1 / 4 : ℝ) (1 / 2))
    (hτ : tauCurve Cd = d) :
    (∀ h : ℝ → ℝ, IsControl h →
      (recipX d h < 1 / d →
        ∃! C, C ∈ Ioo 0 (Cbar d) ∧ Dq C (Yd d C) = 1 / (1 + recipX d h)) ∧
      ∀ C, ((recipX d h < 1 / d ∧ C ∈ Ioo 0 (Cbar d) ∧ Dq C (Yd d C) = 1 / (1 + recipX d h)) ∨
          (recipX d h = 1 / d ∧ C = 0)) →
        IntegrableOn (gapIntegrand d h C) (Ioi 0) ∧
        SCurve Cd - J d h =
          (∫ u in (min C Cd)..(max C Cd), envelopeIntegrand d u) +
            ∫ a in Ioi (0 : ℝ), gapIntegrand d h C a ∧
        0 ≤ (∫ u in (min C Cd)..(max C Cd), envelopeIntegrand d u) +
            ∫ a in Ioi (0 : ℝ), gapIntegrand d h C a) ∧
    IsGreatest {v | ∃ h : ℝ → ℝ, IsControl h ∧ J d h = v} (SCurve Cd) ∧
    IsControl (maxControl Cd) ∧ J d (maxControl Cd) = SCurve Cd ∧
    (∀ h : ℝ → ℝ, IsControl h → J d h = SCurve Cd →
      h =ᵐ[volume.restrict (Icc (0 : ℝ) 1)] maxControl Cd) ∧
    (∀ t ∈ Ico 0 Cd, maxControl Cd t = 0) ∧
    Cd * yE Cd = (1 - 2 * Cd) / (1 - Cd) ∧
    StrictMonoOn (maxControl Cd) (Icc Cd (Cd * (1 + yE Cd))) ∧
    maxControl Cd (Cd * (1 + yE Cd)) = 1 ∧
    1 - Cd * (1 + yE Cd) = Cd ^ 2 / (1 - Cd) ∧
    (∀ t ∈ Ioc (Cd * (1 + yE Cd)) 1, maxControl Cd t = 1) ∧
    ∀ y ∈ Icc 0 (yE Cd),
      gState d (maxControl Cd) (Cd * (1 + y)) =
          d * Real.sqrt (Dq Cd y) * Real.exp (ICrun Cd y / 2) ∧
      maxControl Cd (Cd * (1 + y)) = y * gState d (maxControl Cd) (Cd * (1 + y)) / Dq Cd y := by sorry

end FixedPriceTrade
