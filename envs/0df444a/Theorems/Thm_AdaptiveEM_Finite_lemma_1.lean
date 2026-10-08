-- Prove2me | Theorems.Thm_AdaptiveEM_Finite_lemma_1
-- name    : AdaptiveEM.Finite.lemma_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:06:44.405341+00:00
-- url     : https://prove2.me/theorems/83d79477-05d0-4692-8455-c67aca50ccce
-- title:
--   Lemma 1 (SDE stability), p. 529 — E[sup_{0≤t≤T} ‖X_t‖^p] < ∞ for all p > 0 under Assumption 1
-- statement:
--   Let $(\Omega,\mathcal F,\mathbb P)$ be a probability space with a filtration $(\mathcal F_t)_{t\ge0}$ and a $d$-dimensional standard $(\mathcal F_t)$-Brownian motion $W$. Let $f:\mathbb R^m\to\mathbb R^m$ and $g:\mathbb R^m\to\mathbb R^{m\times d}$ satisfy Assumption 1, let $x_0\in\mathbb R^m$ and $T>0$, and let $X$ be a solution on $[0,T]$ of
--   $$dX_t=f(X_t)\,dt+g(X_t)\,dW_t,\qquad X_0=x_0 .$$
--   Then for every $p>0$
--   $$\mathbb E\Big[\sup_{0\le t\le T}\|X_t\|^p\Big]<\infty .$$
--
--   Finite moments of the running maximum of the solution are needed in the error analysis of Theorem 3, where they control the terms that involve $X$.
--
--   **Formalization Note** $X$ is any process satisfying the published solution relation: continuous on $[0,T]$, adapted to the completed filtration, with $X_t=x_0+\int_0^tf(X_s)ds+\int_0^tg(X_s)dW_s$ for all $t\le T$ almost surely. Existence and uniqueness are not part of the claim. The expectation is a $[0,\infty]$-valued integral of the extended norm.
-- source:
--   Fang, Giles, Adaptive Euler–Maruyama method for SDEs with nonglobally Lipschitz drift, Ann. Appl. Probab. 30 (2020), p. 529, Lemma 1

import Mathlib
import Definitions.Def_EthierKurtz_SDEState
import Definitions.Def_SabanisEuler_Shared_Setting
import Definitions.Def_AdaptiveEM_Finite_Assumptions

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

namespace AdaptiveEM.Finite

open EthierKurtz

/-- Fang–Giles (2020), Lemma 1 (SDE stability), p. 529: under Assumption 1, every solution of
`dX = f(X) dt + g(X) dW`, `X_0 = x0`, on `[0, T]` has `E[sup_{0≤t≤T} ‖X_t‖^p] < ∞` for all
`p > 0`. -/
theorem lemma_1 {m d : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ≥0 mΩ)
    (W : ℝ≥0 → Ω → SDEState d) (hW : SabanisEuler.Shared.IsWienerMartingale P ℱ W)
    (f : SDEState m → SDEState m) (g : SDEState m → SabanisEuler.Shared.Diffusion m d)
    (α₁ β₁ : ℝ) (hA1 : Assumption1 f g α₁ β₁)
    (x0 : SDEState m) (T : ℝ≥0) (hT : 0 < T) (X : ℝ≥0 → Ω → SDEState m)
    (hX : SabanisEuler.Shared.IsSolution P ℱ W T (fun _ => x0) (fun z => f z.2)
      (fun z => g z.2) X) :
    ∀ p : ℝ, 0 < p →
      ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ≥0) T, ‖X t ω‖ₑ) ^ p ∂P < ∞ := by sorry

end AdaptiveEM.Finite
