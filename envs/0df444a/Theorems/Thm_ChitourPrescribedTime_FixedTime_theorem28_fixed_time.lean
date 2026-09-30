-- Prove2me | Theorems.Thm_ChitourPrescribedTime_FixedTime_theorem28_fixed_time
-- name    : ChitourPrescribedTime.FixedTime.theorem28_fixed_time
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-28T00:10:00.522979+00:00
-- url     : https://prove2.me/theorems/0ab66cfd-65ef-4a99-aa12-7cdf1143dc63
-- title:
--   Theorem 28 — the varying-degree feedback $\omega^H_{\kappa(x)}(x)$ is globally fixed-time stabilizing with settling time bounded by (52)
-- statement:
--   Let $n\ge1$, let the gains $\ell_1,\dots,\ell_n>0$ and the constant $C>0$ satisfy the decay inequality (36), and let $0<\underline b\le\bar b$. Then there exist $m\in(0,1)$ and $\kappa_0\in(0,\tfrac1{2n})$, with $r(m,\kappa_0)>0$ and $r(m,-\kappa_0)>0$, such that for every measurable $b:[0,\infty)\to\mathbb R$ with
--   $$\bar b\ge b(t)\ge\underline b,\qquad t\ge0,$$
--   the chain of integrators with uncertain input gain and adapted feedback
--   $$\dot x=J_nx+b(t)\,\frac{\omega^H_{\kappa(x)}(x)}{\underline b}\,e_n$$
--   is globally fixed-time stable at the origin with settling time at most
--   $$T^\ast(m,\kappa_0)=\frac1C\left(\frac{r(m,\kappa_0)^{-\alpha(\kappa_0)}}{\alpha(\kappa_0)}-2\ln(2m)+\frac{r(m,-\kappa_0)^{-\alpha(-\kappa_0)}}{-\alpha(-\kappa_0)}\right).$$
--
--   Here $\kappa(\cdot)$ is the state-dependent degree (49) and $r(m,\pm\kappa_0)$ are the radii of Theorem 28. This is the fixed-time result from which Theorem 30 is obtained by rescaling.
--
--   **Formalization Note** (51) prints $\dot x=J_nx+b(t)u(t)$ without $e_n$, a slip: the control enters through $e_n$ as in (1) and (31). The page explains "adapted" as the feedback $\omega^H_{\kappa(x)}(x)/\underline b$; that is the feedback used. Measurability of $b$ is added so that Carathéodory solutions exist, which Definition 1(a) requires. The gains and $C$ are data satisfying (36) (from Proposition 24), not existentially chosen: with an unconstrained $C$ the bound would be false. $m$ and $\kappa_0$ are chosen after $\underline b,\bar b$, as on the page.
-- source:
--   Chitour, Ushirobira, Bouhemou, Stabilization for a Perturbed Chain of Integrators in Prescribed Time, SIAM J. Control Optim. 58 (2020), pp. 1036–1037, Theorem 28, eqs. (50)–(52)

import Mathlib
import Definitions.Def_ChitourPrescribedTime_FixedTime_Stability
import Definitions.Def_ChitourPrescribedTime_FixedTime_PureChain
import Definitions.Def_ChitourPrescribedTime_FixedTime_Feedback
import Definitions.Def_ChitourPrescribedTime_FixedTime_Lyapunov
import Definitions.Def_ChitourPrescribedTime_FixedTime_VaryingDegree

namespace ChitourPrescribedTime.FixedTime

/-- Theorem 28 (pp. 1036–1037). Let the gains `ℓ` and the constant `C > 0` satisfy (36), and let
`0 < b̲ ≤ b̄`. There are `m ∈ (0, 1)` and `κ₀ ∈ (0, 1/(2n))` with `r(m, ±κ₀) > 0` such that for
every measurable `b` with `b̲ ≤ b(t) ≤ b̄` (`t ≥ 0`), the system
`ẋ = J_n x + b(t) ω^H_{κ(x)}(x)/b̲ e_n` is globally fixed-time stable at the origin with settling
time at most the right-hand side of (52). -/
theorem theorem28_fixed_time (n : ℕ) (hn : 1 ≤ n) (ℓ : Fin n → ℝ) (hℓ : ∀ j, 0 < ℓ j)
    (C : ℝ) (hC : 0 < C) (h36 : Decay36 ℓ C)
    (bLow bUp : ℝ) (hbLow : 0 < bLow) (hbUp : bLow ≤ bUp) :
    ∃ m ∈ Set.Ioo (0 : ℝ) 1, ∃ κ0 ∈ Set.Ioo (0 : ℝ) (1 / (2 * (n : ℝ))),
      0 < rPlus ℓ m κ0 ∧ 0 < rMinus ℓ m κ0 ∧
      ∀ b : ℝ → ℝ, Measurable b → (∀ t : ℝ, 0 ≤ t → bLow ≤ b t ∧ b t ≤ bUp) →
        GloballyFixedTimeStable
          (fun (t : ℝ) (x : EuclideanSpace ℝ (Fin n)) =>
            chainField n x (b t * (omegaH ℓ (kappaOf ℓ m κ0 x) x / bLow)))
          (settlingBound ℓ C m κ0) := by sorry

end ChitourPrescribedTime.FixedTime
