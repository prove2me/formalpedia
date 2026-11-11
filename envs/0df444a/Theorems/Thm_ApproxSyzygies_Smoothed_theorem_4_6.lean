-- Prove2me | Theorems.Thm_ApproxSyzygies_Smoothed_theorem_4_6
-- name    : ApproxSyzygies.Smoothed.theorem_4_6
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T14:02:58.013139+00:00
-- url     : https://prove2.me/theorems/e05426e1-97cd-42e0-bac3-d37807d185f5
-- title:
--   Theorem 4.6 — vector-valued Carbery–Wright [BCPV19]: $\Pr[\|\Pi_Ea^{\otimes D}\|\le c'_D\rho^D/n^{D/2}]\le e^{-c_D\theta n}$
-- statement:
--   For every $D\ge1$ there are constants $c_D,c'_D>0$ such that the following holds. For every $n$, every $\theta\in(0,1)$, every fixed subspace $E\subseteq\mathrm{Sym}^D(\mathbb R^n)$ with $\dim E\ge\theta\binom{n+D-1}{D}$, every fixed $\bar a\in\mathbb R^n$ and every $\rho>0$,
--   $$\Pr_{a\sim N(\bar a,\rho^2I)}\Big[\big\|\Pi_Ea^{\otimes D}\big\|_2\le c'_D\frac{\rho^D}{n^{D/2}}\Big]\le\exp(-c_D\theta n).$$
--   The paper cites it from Bhaskara, Chen, Perreault and Vijayaraghavan (STOC 2019, Theorem 4.1). In the proof of Theorem 4.1 it gives the subspace anticoncentration of $(v^{(\ell)}_i)^{D_i}$ required by Proposition 4.8.
--
--   Differences from the source:
--   - encoding: $\mathrm{Sym}^D(\mathbb R^n)$, $a^{\otimes D}$, $\|\cdot\|_2$ → `symTensors n D` (slot-permutation-invariant tensors in $\mathbb R^{[n]^D}$), `tensPow`, the Frobenius norm; reason: the standard model of symmetric tensors
--   - encoding: $a\sim N(\bar a,\rho^2I)$ → $a=\bar a+\rho g$ with $g$ distributed as $n$ independent $N(0,1)$ (`Measure.pi`); reason: the same law
--   - reading: $\rho$ (not quantified in the statement) → every $\rho>0$, with $c_D,c'_D$ chosen before $\rho$; reason: the constants depend only on $D$; $\rho$ is the smoothing scale of §3
-- source:
--   Bhaskara, Guo, Sinha, Srinivas, Vijayaraghavan, Approximate Syzygies of Smoothed Polynomials and Applications, STOC 2027 submission (manuscript sha256 9c17d04e…), p. 32, Theorem 4.6

import Mathlib
import Definitions.Def_ApproxSyzygies_Smoothed_Anticoncentration

open MeasureTheory ProbabilityTheory

namespace ApproxSyzygies.Smoothed

/-- Theorem 4.6 (p. 32; Theorem 4.1 of [BCPV19]): vector-valued Carbery–Wright inequality. For
every `D ≥ 1` there are `c_D, c'_D > 0` such that for every `θ ∈ (0, 1)`, every subspace `E` of
`Sym^D(ℝ^n)` of dimension at least `θ · binom(n+D−1, D)`, every `ā ∈ ℝ^n` and every `ρ > 0`,
`P_{a ∼ N(ā, ρ² I)}[‖Π_E a^{⊗D}‖₂ ≤ c'_D ρ^D / n^{D/2}] ≤ exp(−c_D θ n)`. The Gaussian is
`a = ā + ρ g` with `g` a vector of `n` independent `N(0, 1)`. -/
theorem theorem_4_6 (D : ℕ) (hD : 1 ≤ D) :
    ∃ cD : ℝ, 0 < cD ∧ ∃ cD' : ℝ, 0 < cD' ∧
      ∀ (n : ℕ) (θ : ℝ), 0 < θ → θ < 1 →
        ∀ E : Submodule ℝ (EuclideanSpace ℝ (Fin D → Fin n)), E ≤ symTensors n D →
          θ * ((n + D - 1).choose D : ℝ) ≤ (Module.finrank ℝ E : ℝ) →
          ∀ (abar : Fin n → ℝ) (ρ : ℝ), 0 < ρ →
            (Measure.pi fun _ : Fin n => gaussianReal 0 1)
                {g | ‖E.starProjection (tensPow (abar + ρ • g) D)‖ ≤
                    cD' * ρ ^ D / (n : ℝ) ^ ((D : ℝ) / 2)}
              ≤ ENNReal.ofReal (Real.exp (-(cD * θ * n))) := by sorry

end ApproxSyzygies.Smoothed
