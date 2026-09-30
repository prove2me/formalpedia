-- Prove2me | Theorems.Thm_ChitourPrescribedTime_FixedTime_proposition33_explicit_kappa0
-- name    : ChitourPrescribedTime.FixedTime.proposition33_explicit_kappa0
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:09:28.190986+00:00
-- url     : https://prove2.me/theorems/6472cbd6-d894-465e-8d47-ab2cfbe75bcd
-- title:
--   Proposition 33 — for every $m$ a threshold $\kappa_0(m)$ below which Theorems 28 and 30 hold
-- statement:
--   Let $n\ge1$, let the gains $\ell$ and the constant $C>0$ satisfy (36), and let $0<\underline b\le\bar b$. For every $m\in(0,1)$ there is $\kappa_0(m)\in(0,\tfrac1{2n}]$ such that for every $\kappa_0\in(0,\kappa_0(m))$, with $\kappa(\cdot)$ the degree of (49):
--
--   1. for every $\beta\in[\underline b,\bar b]$ and every $x\in B^0_{1-m,1+m}$, the derivative of $V_0$ along $\dot x=J_nx+\beta\,\omega^H_{\kappa(x)}(x)/\underline b\;e_n$ satisfies $\dot V_0(x)\le-\tfrac C2V_0(x)$;
--   2. $r(m,\kappa_0)>0$, $r(m,-\kappa_0)>0$, and for every measurable $b$ with $\underline b\le b(t)\le\bar b$ ($t\ge0$), the system
--   $$\dot x=J_nx+b(t)\,\frac{\omega^H_{\kappa(x)}(x)}{\underline b}\,e_n$$
--   is globally fixed-time stable at the origin with settling time at most
--   $$T^*(m,\kappa_0)=\frac1C\left(\frac{r(m,\kappa_0)^{-\alpha(\kappa_0)}}{\alpha(\kappa_0)}+\max\Big(-2\ln(2m),\,2\ln\frac{1+m}{1-m}\Big)+\frac{r(m,-\kappa_0)^{-\alpha(-\kappa_0)}}{-\alpha(-\kappa_0)}\right)$$
--   (the statement of Theorem 28), where $r(m,\pm\kappa_0)$ and $\alpha$ are as in (52) and (36);
--   3. for every $T>0$ and $\lambda>0$ with $\lambda\ge T^*(m,\kappa_0)/T$, the feedback $\omega^H_{\kappa(D^{\mathbf r}_\lambda x)}(D^{\mathbf r}_\lambda x)$ renders the pure chain (31) globally fixed-time stable with settling time at most $T$ (the statement of Theorem 30).
--
--   This makes the choice of $\kappa_0$ in Theorems 28 and 30 quantitative for every $m$.
--
--   **Formalization Note** The page prints $\kappa_0(m)\in[-\tfrac1{2n},-\tfrac1{2n}]$, a slip: its formula on p. 1041 is positive, and $\kappa_0$ must lie in $(0,\tfrac1{2n})$. The page's proof bounds the crossing time of the shell $B^0_{1-m,1+m}$ by $-2\ln(2m)/C$, which follows from item 1 only when $2\ln\frac{1+m}{1-m}\le-2\ln(2m)$, i.e. $m\le(\sqrt{17}-3)/4$; the time that item 1 actually gives is $\frac2C\ln\frac{1+m}{1-m}$. The bound $T^*$ therefore takes the larger of the two middle terms: it equals the right-hand side of (52) for $m\le(\sqrt{17}-3)/4$ and is the bound the proof supports for larger $m$. Item 1 is the displayed claim of the proof ($\dot V_0\le -CV_0/2$ inside $B^0_{1-m,1+m}$). As in Theorem 28, "adapted" means the feedback divided by $\underline b$, and $b$ is assumed measurable so that Carathéodory solutions exist. Indices are 1-based on the page and 0-based on `Fin n`.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), pp. 1040–1041, Proposition 33 and its proof

import Mathlib
import Definitions.Def_ChitourPrescribedTime_FixedTime_Stability
import Definitions.Def_ChitourPrescribedTime_FixedTime_PureChain
import Definitions.Def_ChitourPrescribedTime_FixedTime_Feedback
import Definitions.Def_ChitourPrescribedTime_FixedTime_Lyapunov
import Definitions.Def_ChitourPrescribedTime_FixedTime_VaryingDegree

namespace ChitourPrescribedTime.FixedTime

/-- Proposition 33 (p. 1040), with the settling-time bound its proof establishes. Let the gains
`ℓ` and the constant `C > 0` satisfy (36), and let `0 < b̲ ≤ b̄`. For every `m ∈ (0, 1)` there is
`κ₀(m) ∈ (0, 1/(2n)]` such that for every `κ₀ ∈ (0, κ₀(m))`:
(i) along `ẋ = J_n x + β ω^H_{κ(x)}(x)/b̲ e_n`, for every `β ∈ [b̲, b̄]`, one has
`V̇_0 ≤ -(C/2) V_0` on `B^0_{1-m,1+m}`;
(ii) `r(m, κ₀) > 0`, `r(m, -κ₀) > 0`, and for every measurable `b` with `b̲ ≤ b ≤ b̄` the system
(51) with the adapted feedback `ω^H_{κ(x)}(x)/b̲` is globally fixed-time stable with settling
time at most
`T* = (1/C) ( r(m,κ₀)^{-α(κ₀)}/α(κ₀) + max(-2 ln(2m), 2 ln((1+m)/(1-m))) + r(m,-κ₀)^{-α(-κ₀)}/(-α(-κ₀)) )`,
which is the right-hand side of (52) whenever `m ≤ (√17 - 3)/4` (the statement of Theorem 28);
(iii) for every `T > 0` and `λ > 0` with `T* ≤ λT`, the feedback `ω^H_{κ(D_λ x)}(D^r_λ x)`
renders (31) globally fixed-time stable with settling time `≤ T` (the statement of Theorem 30). -/
theorem proposition33_explicit_kappa0 (n : ℕ) (hn : 1 ≤ n) (ℓ : Fin n → ℝ)
    (hℓ : ∀ j, 0 < ℓ j) (C : ℝ) (hC : 0 < C) (h36 : Decay36 ℓ C)
    (bLow bUp : ℝ) (hbLow : 0 < bLow) (hbUp : bLow ≤ bUp)
    (m : ℝ) (hm : m ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ κbar : ℝ, 0 < κbar ∧ κbar ≤ 1 / (2 * (n : ℝ)) ∧
      ∀ κ0 ∈ Set.Ioo (0 : ℝ) κbar,
        (∀ β ∈ Set.Icc bLow bUp, ∀ x : EuclideanSpace ℝ (Fin n),
          1 - m ≤ lyapV ℓ 0 x → lyapV ℓ 0 x ≤ 1 + m →
            fderiv ℝ (lyapV ℓ 0) x
                (chainField n x (β * (omegaH ℓ (kappaOf ℓ m κ0 x) x / bLow)))
              ≤ -(C / 2) * lyapV ℓ 0 x) ∧
        0 < rPlus ℓ m κ0 ∧ 0 < rMinus ℓ m κ0 ∧
        (∀ b : ℝ → ℝ, Measurable b → (∀ t : ℝ, 0 ≤ t → bLow ≤ b t ∧ b t ≤ bUp) →
          GloballyFixedTimeStable
            (fun (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) =>
              chainField n x (b t * (omegaH ℓ (kappaOf ℓ m κ0 x) x / bLow)))
            ((1 / C) * (rPlus ℓ m κ0 ^ (-alpha κ0) / alpha κ0
              + max (-2 * Real.log (2 * m)) (2 * Real.log ((1 + m) / (1 - m)))
              + rMinus ℓ m κ0 ^ (-alpha (-κ0)) / (-alpha (-κ0))))) ∧
        ∀ T : ℝ, 0 < T → ∀ lam : ℝ, 0 < lam →
          (1 / C) * (rPlus ℓ m κ0 ^ (-alpha κ0) / alpha κ0
              + max (-2 * Real.log (2 * m)) (2 * Real.log ((1 + m) / (1 - m)))
              + rMinus ℓ m κ0 ^ (-alpha (-κ0)) / (-alpha (-κ0))) ≤ lam * T →
            GloballyFixedTimeStable
              (fun (_ : ℝ) (x : EuclideanSpace ℝ (Fin n)) =>
                chainField n x (omegaH ℓ (kappaOf ℓ m κ0 (dilR n lam x)) (dilR n lam x))) T := by sorry

end ChitourPrescribedTime.FixedTime
