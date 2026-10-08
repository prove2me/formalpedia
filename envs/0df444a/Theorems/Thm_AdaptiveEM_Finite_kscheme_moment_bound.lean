-- Prove2me | Theorems.Thm_AdaptiveEM_Finite_kscheme_moment_bound
-- name    : AdaptiveEM.Finite.kscheme_moment_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:07:43.895978+00:00
-- url     : https://prove2.me/theorems/902bab25-90d7-4fcc-a6ad-26e4eb8050f4
-- title:
--   §6.1 Step 3, p. 550 — E[sup_{0≤t≤T} ‖X̂^K_t‖^p] ≤ C_{p,T}, uniformly in K > ‖X_0‖ and in h
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$, $(\mathcal F_t)$ and a $d$-dimensional standard $(\mathcal F_t)$-Brownian motion $W$ be given, let $f,g$ satisfy Assumption 1, fix constants $\alpha,\beta$, an initial value $x_0$ and $T>0$. For every $p\ge4$ there is a constant $C_{p,T}$ such that for every timestep function $h$ satisfying Assumption 2 with the constants $\alpha,\beta$, and every $K>\|x_0\|$, the continuous K-scheme approximation $\widehat X^K$ satisfies
--   $$\mathbb E\Big[\sup_{0\le t\le T}\|\widehat X^K_t\|^p\Big]\le C_{p,T} .$$
--
--   The bound is independent of $K$; letting $K\to\infty$ by monotone convergence then gives the moment bound of Theorem 1 for the unprojected scheme.
--
--   **Formalization Note** The constant is chosen before $h$ and $K$ (it may depend on $p$, $T$, $x_0$, $f$, $g$, the constants of both assumptions and the probability space, but not on $h$ or $K$). The paper gives the proof for $p\ge4$ and obtains $0<p<4$ by Hölder's inequality; this intermediate step is stated for $p\ge4$, as in the proof. The expectation is a $[0,\infty]$-valued integral.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 550, §6.1, proof of Theorem 1, Step 3

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Assumptions
import Definitions.Def_AdaptiveEM_Finite_Scheme
import Definitions.Def_AdaptiveEM_Finite_KScheme

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace AdaptiveEM.Finite

open EthierKurtz

/-- Fang–Giles (2020), §6.1, proof of Theorem 1, Step 3, p. 550: under Assumption 1, for every
`p ≥ 4` there is a constant `C_{p,T}` such that for every timestep function `h` satisfying
Assumption 2 with the fixed constants `α, β`, and every `K > ‖x0‖`,
`E[sup_{0≤t≤T} ‖X̂^K_t‖^p] ≤ C_{p,T}`. -/
theorem kscheme_moment_bound {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : SabanisEuler.Shared.IsWienerMartingale P ℱ W)
    (f : SDEState m → SDEState m) (g : SDEState m → SabanisEuler.Shared.Diffusion m d)
    (α₁ β₁ : ℝ) (hA1 : Assumption1 f g α₁ β₁) (α β : ℝ)
    (x0 : SDEState m) (T : ℝ≥0) (hT : 0 < T) :
    ∀ p : ℝ, 4 ≤ p → ∃ C : ℝ, ∀ h : SDEState m → ℝ, Assumption2 f h α β →
      ∀ K : ℝ, ‖x0‖ < K →
        ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ‖XhatK f g h x0 W K t ω‖ₑ) ^ p ∂P
          ≤ ENNReal.ofReal C := by sorry

end AdaptiveEM.Finite
