-- Prove2me | Theorems.Thm_CubeSampling_proposition_E_2
-- name    : CubeSampling.proposition_E_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:20:08.816931+00:00
-- url     : https://prove2.me/theorems/13a7fffb-b4fd-4b47-b154-6464cbaec3c9
-- title:
--   Proposition E.2 — estimator-independent parametric obstruction
-- statement:
--   **Proposition E.2.** Fix $A \ge 16$. There is $\rho_A > 0$ with the following property. Let $\Phi$ be an orthonormal family of $m \ge 1$ functions on $\{-1,1\}^d$ spanning $V$, let $E$ satisfy $p = \mu_d(E) \in (0, 1/2]$, $\rho \le \rho_A$, $\sigma > 0$ and $t \ge \log 4$. Suppose either
--   $$
--   \mathbb E[\Phi(X)\Phi(X)^\top\mathbf 1\{X\notin E\}] \preceq \rho I_m,
--   $$
--   or $t \ge m$ and some unit vector $v$ satisfies $\mathbb E[(v^\top\Phi)^2\mathbf 1_{E^c}] \le \rho$ (the directional assumption of Lemma 6.1(ii)). Then for every positive integer $n \le (m+t)/(1024p)$, the Gaussian model satisfies
--   $$
--   R^*_{n,e^{-t}}(V) > A\sigma^2\,\frac{m+t}{n}.
--   $$
--
--   Differences from the source:
--   - encoding: an m-dimensional subspace V with its orthonormal basis Φ_V → an orthonormal family Φ : Fin m → (cube → ℝ); reason: the paper notes the choice of basis is arbitrary; V = span Φ
--   - generalization: V ⊆ P_{d,k} (the standing setup of §1.1) → V the span of any orthonormal family of functions on the cube; reason: the statement and its proof use only orthonormality; it specializes to V ⊆ P_{d,k}
--   - reading: V of dimension m → 1 ≤ m; reason: a model of dimension 0 has risk 0; the proposition concerns models V ≠ 0
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Proposition E.2, p.35

import Mathlib
import Definitions.Def_CubeSampling_minimaxRisk
import Definitions.Def_CubeSampling_IsOrthonormalFamily
import Definitions.Def_CubeSampling_cubeProb
import Definitions.Def_CubeSampling_outsideEnergy
import Definitions.Def_CubeSampling_outsideCov
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- Proposition E.2 (estimator-independent parametric obstruction) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Proposition E.2, p.35): fix
`A ≥ 16`. There is `ρ_A > 0` such that, with `p = μ_d(E) ∈ (0, 1/2]`, under `E[Φ(X)Φ(X)^⊤ 1{X ∉ E}] ⪯ ρ I_m`, or
under the directional assumption of Lemma 6.1(ii) when `t ≥ m`, with `ρ ≤ ρ_A`, for every `t ≥ log 4` and every
positive integer `n ≤ (m + t)/(1024p)`, the Gaussian model satisfies `R*_{n,e^{−t}}(V) > Aσ² (m + t)/n`.

**Formalization Note** `V` (orthonormal basis `Φ`, `m ≥ 1`) is any space of functions on the cube;
`σ > 0`; the standing assumption of Appendix E, `P(E) = p ∈ (0, 1/2]`, is a hypothesis. -/
theorem proposition_E_2 (A : ℝ) (hA : 16 ≤ A) :
    ∃ ρA : ℝ, 0 < ρA ∧ ∀ (d m : ℕ) (Φ : Fin m → Cube d → ℝ), IsOrthonormalFamily Φ → 1 ≤ m →
      ∀ E : Set (Cube d), 0 < cubeProb d E → cubeProb d E ≤ 1 / 2 →
      ∀ ρ : ℝ, ρ ≤ ρA → ∀ σ : ℝ, 0 < σ → ∀ t : ℝ, Real.log 4 ≤ t →
      ((ρ • (1 : Matrix (Fin m) (Fin m) ℝ) - outsideCov d Φ E).PosSemidef ∨
        ((m : ℝ) ≤ t ∧ ∃ v : Fin m → ℝ, ∑ j, v j ^ 2 = 1 ∧
          outsideEnergy d E (fun x => ∑ j, v j * Φ j x) ≤ ρ)) →
      ∀ n : ℕ, 1 ≤ n → (n : ℝ) ≤ (m + t) / (1024 * cubeProb d E) →
        ENNReal.ofReal (A * σ ^ 2 * (m + t) / n) < minimaxRisk Φ σ n (Real.exp (-t)) := by sorry

end CubeSampling
