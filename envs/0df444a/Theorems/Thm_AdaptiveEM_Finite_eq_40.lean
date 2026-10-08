-- Prove2me | Theorems.Thm_AdaptiveEM_Finite_eq_40
-- name    : AdaptiveEM.Finite.eq_40
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:37.139198+00:00
-- url     : https://prove2.me/theorems/127e057b-fbaf-4965-afa0-623d1c83d390
-- title:
--   (40), p. 552 — E[sup_{s≤t} ‖e_s‖^p] ≤ C¹∫₀ᵗ E[sup_{u≤s} ‖e_u‖^p] ds + C²∫₀ᵗ (E‖X̂_s − X̄_s‖^{2p})^{1/2} ds
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$, $(\mathcal F_t)$ and a $d$-dimensional standard $(\mathcal F_t)$-Brownian motion $W$ be given. Let $f,g$ satisfy Assumption 4, let $h$ satisfy Assumption 2, let $T>0$, let the family $h^\delta$, $0<\delta\le1$, satisfy Assumption 3 with each $h^\delta$ measurable, and let $X$ be a solution on $[0,T]$ of $dX_t=f(X_t)dt+g(X_t)dW_t$, $X_0=x_0$. Write $\widehat X,\overline X$ for the interpolants of the scheme (5) run with $h^\delta$ from $x_0$, and $e_t=\widehat X_t-X_t$. For every $p\ge4$ there are constants $C^1_{p,T},C^2_{p,T}$ such that for all $\delta\in(0,1]$ and all $t\in[0,T]$
--   $$\mathbb E\Big[\sup_{0\le s\le t}\|e_s\|^p\Big]\le C^1_{p,T}\int_0^t\mathbb E\Big[\sup_{0\le u\le s}\|e_u\|^p\Big]ds+C^2_{p,T}\int_0^t\Big(\mathbb E\big[\|\widehat X_s-\overline X_s\|^{2p}\big]\Big)^{1/2}ds .$$
--
--   This is the integral inequality for the error to which Grönwall's inequality is applied once the second integral has been bounded by the previous milestone.
--
--   **Formalization Note** The constants are chosen before $\delta$ and $t$. Expectations and the time integrals are $[0,\infty]$-valued; the time integrals are Lebesgue integrals over $s\in[0,t]\subset\mathbb R$. Measurability of each $h^\delta$ is an added regularity hypothesis. The statement is for $p\ge4$, the range in which the paper's proof is given.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 552, §6.2, proof of Theorem 3, (40)

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Assumptions
import Definitions.Def_AdaptiveEM_Finite_Scheme

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace AdaptiveEM.Finite

open EthierKurtz

/-- Fang–Giles (2020), §6.2, proof of Theorem 3, (40), p. 552: with `e_t = X̂_t - X_t`, for every
`p ≥ 4` there are constants `C¹_{p,T}, C²_{p,T}` (independent of `δ`) such that for all
`δ ∈ (0, 1]` and `t ∈ [0, T]`
`E[sup_{0≤s≤t} ‖e_s‖^p] ≤ C¹ ∫_0^t E[sup_{0≤u≤s} ‖e_u‖^p] ds + C² ∫_0^t (E[‖X̂_s - X̄_s‖^{2p}])^{1/2} ds`. -/
theorem eq_40 {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : SabanisEuler.Shared.IsWienerMartingale P ℱ W)
    (f : SDEState m → SDEState m) (g : SDEState m → SabanisEuler.Shared.Diffusion m d)
    (α γ μ q : ℝ) (hA4 : Assumption4 f g α γ μ q)
    (h : SDEState m → ℝ) (α' β' : ℝ) (hA2 : Assumption2 f h α' β')
    (x0 : SDEState m) (T : ℝ≥0) (hT : 0 < T)
    (hδ : ℝ → SDEState m → ℝ) (hA3 : Assumption3 (T : ℝ) h hδ)
    (hδ_meas : ∀ δ : ℝ, 0 < δ → δ ≤ 1 → Measurable (hδ δ))
    (X : ℝ≥0 → Ω → SDEState m)
    (hX : SabanisEuler.Shared.IsSolution P ℱ W T (fun _ => x0) (fun z => f z.2)
      (fun z => g z.2) X) :
    ∀ p : ℝ, 4 ≤ p → ∃ C1 C2 : ℝ, ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
      ∀ t ∈ Set.Icc (0 : ℝ≥0) T,
        ∫⁻ ω, (⨆ s ∈ Set.Icc (0 : ℝ≥0) t, ‖Xhat f g (hδ δ) x0 W s ω - X s ω‖ₑ) ^ p ∂P
          ≤ ENNReal.ofReal C1 * ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
                ∫⁻ ω, (⨆ u ∈ Set.Icc (0 : ℝ≥0) s.toNNReal,
                  ‖Xhat f g (hδ δ) x0 W u ω - X u ω‖ₑ) ^ p ∂P
            + ENNReal.ofReal C2 * ∫⁻ s in Set.Icc (0 : ℝ) (t : ℝ),
                (∫⁻ ω, ‖Xhat f g (hδ δ) x0 W s.toNNReal ω
                  - Xbar f g (hδ δ) x0 W s.toNNReal ω‖ₑ ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) := by sorry

end AdaptiveEM.Finite
