-- Prove2me | Theorems.Thm_BanditAlgorithm_elliptical_potential_lemma
-- name    : BanditAlgorithm.elliptical_potential_lemma
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-07-29T16:38:45.348988+00:00
-- url     : https://prove2.me/theorems/900f2237-69b9-4697-b303-9f34de80e938
-- statement:
--   (Elliptical potential lemma) Let $V_0 \in \mathbb{R}^{d\times d}$ be positive definite and $a_1,\dots,a_n \in \mathbb{R}^d$ with $\|a_t\|_2 \le L$ for all $t\in[n]$, and set $V_t = V_0 + \sum_{s\le t}a_sa_s^\top$. Then
--
--   $$\sum_{t=1}^n \big(1 \wedge \|a_t\|^2_{V_{t-1}^{-1}}\big) \le 2\log\frac{\det V_n}{\det V_0} \le 2d\log\frac{\mathrm{tr}\,V_0 + nL^2}{d\,\det(V_0)^{1/d}}$$
--
--   — both inequalities, as a conjunction. Purely deterministic.
-- source:
--   L&S Lemma 19.4, p.243

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real


open Matrix

theorem BanditAlgorithm.elliptical_potential_lemma {d n : ℕ} (hd : 0 < d)
    {V₀ : Matrix (Fin d) (Fin d) ℝ} (hV₀ : V₀.PosDef)
    {L : ℝ} (a : ℕ → Fin d → ℝ)
    (ha : ∀ t ∈ Finset.range n, Real.sqrt (a (t + 1) ⬝ᵥ a (t + 1)) ≤ L) :
    ∑ t ∈ Finset.range n,
        min 1 (a (t + 1) ⬝ᵥ
          (V₀ + ∑ s ∈ Finset.range t,
            vecMulVec (a (s + 1)) (a (s + 1)))⁻¹ *ᵥ a (t + 1)) ≤
      2 * Real.log
        ((V₀ + ∑ s ∈ Finset.range n,
          vecMulVec (a (s + 1)) (a (s + 1))).det / V₀.det) ∧
    2 * Real.log
        ((V₀ + ∑ s ∈ Finset.range n,
          vecMulVec (a (s + 1)) (a (s + 1))).det / V₀.det) ≤
      2 * d * Real.log
        ((V₀.trace + n * L ^ 2) / (d * V₀.det ^ ((1 : ℝ) / d))) := by
  sorry
