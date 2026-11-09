-- Prove2me | Theorems.Thm_CubeSampling_lemma_6_1
-- name    : CubeSampling.lemma_6_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:17:29.031942+00:00
-- url     : https://prove2.me/theorems/0101020a-49d0-49f9-a733-2592b0021372
-- title:
--   Lemma 6.1 — many small empirical eigenvalues
-- statement:
--   **Lemma 6.1.** Let $\Phi$ be an orthonormal family of $m$ functions on $\{-1,1\}^d$, $E \subseteq \{-1,1\}^d$ with $p = \mu_d(E) \in (0,1/2]$, and let $\hat\Sigma$ be the empirical covariance of $X_1,\dots,X_n$ i.i.d. $\mu_d$.
--
--   1. If $\mathbb E[\Phi(X)\Phi(X)^\top\mathbf 1\{X\notin E\}] \preceq \rho I_m$, $m \ge 2$, and $n \le m/(128p)$, then with probability at least $15/16$, at least $\lfloor m/2\rfloor$ eigenvalues of $\hat\Sigma$ (counted with multiplicity) are at most $128\rho$.
--   2. If $t \ge \log 4$, $n \le t/(512p)$, and a fixed unit vector $v$ satisfies $\mathbb E[(v^\top\Phi)^2\mathbf 1_{E^c}] \le \rho$, then with probability at least $(15/16)e^{-t/256}$ the smallest eigenvalue of $\hat\Sigma$ is at most $32\rho$.
--
--   Small empirical eigenvalues force a large minimax error through Theorem 2.1; this is the mechanism of the lower bound.
--
--   Differences from the source:
--   - encoding: an m-dimensional subspace V with its orthonormal basis Φ_V → an orthonormal family Φ : Fin m → (cube → ℝ); reason: the paper notes the choice of basis is arbitrary; V = span Φ
--   - encoding: the smallest eigenvalue of Σ̂ is at most 32ρ → some eigenvalue of Σ̂ (with multiplicity) is at most 32ρ; reason: equivalent statements
--   - generalization: V ⊆ P_{d,k} (the standing setup of §1.1) → V the span of any orthonormal family of functions on the cube; reason: the statement and its proof use only orthonormality; it specializes to V ⊆ P_{d,k}
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Lemma 6.1, p.22

import Mathlib
import Definitions.Def_CubeSampling_IsOrthonormalFamily
import Definitions.Def_CubeSampling_cubeMeasure
import Definitions.Def_CubeSampling_cubeProb
import Definitions.Def_CubeSampling_outsideEnergy
import Definitions.Def_CubeSampling_outsideCov
import Definitions.Def_CubeSampling_empCov
open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace CubeSampling

/-- Lemma 6.1 (many small empirical eigenvalues) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Lemma 6.1, p.22): let `p = μ_d(E) ∈ (0, 1/2]`.
(i) If `E[Φ(X)Φ(X)^⊤ 1{X ∉ E}] ⪯ ρ I_m`, `m ≥ 2` and `n ≤ m/(128p)`, then with probability at least `15/16`,
at least `⌊m/2⌋` eigenvalues of `Σ̂` are at most `128ρ`. (ii) If `t ≥ log 4`, `n ≤ t/(512p)` and a fixed unit
vector `v` satisfies `E[(v^⊤Φ)² 1_{E^c}] ≤ ρ`, then with probability at least `(15/16) e^{−t/256}` the
smallest eigenvalue of `Σ̂` is at most `32ρ`.

**Formalization Note** Eigenvalues are counted with multiplicity (`Matrix.IsHermitian.eigenvalues`);
"the smallest eigenvalue is at most `32ρ`" is "some eigenvalue is at most `32ρ`"; `X ~ μ_d^n`. -/
theorem lemma_6_1 {d m : ℕ} (Φ : Fin m → Cube d → ℝ) (hΦ : IsOrthonormalFamily Φ)
    (E : Set (Cube d)) (hp : 0 < cubeProb d E) (hp' : cubeProb d E ≤ 1 / 2) (ρ : ℝ) (n : ℕ) :
    ((ρ • (1 : Matrix (Fin m) (Fin m) ℝ) - outsideCov d Φ E).PosSemidef → 2 ≤ m →
        (n : ℝ) ≤ m / (128 * cubeProb d E) →
        ENNReal.ofReal (15 / 16) ≤ (Measure.pi fun _ : Fin n => cubeMeasure d)
          {X | m / 2 ≤ (Finset.univ.filter fun j =>
            (empCov_isHermitian Φ n X).eigenvalues j ≤ 128 * ρ).card}) ∧
    (∀ t : ℝ, Real.log 4 ≤ t → (n : ℝ) ≤ t / (512 * cubeProb d E) →
      ∀ v : Fin m → ℝ, ∑ j, v j ^ 2 = 1 →
        outsideEnergy d E (fun x => ∑ j, v j * Φ j x) ≤ ρ →
        ENNReal.ofReal (15 / 16 * Real.exp (-t / 256)) ≤ (Measure.pi fun _ : Fin n => cubeMeasure d)
          {X | ∃ j, (empCov_isHermitian Φ n X).eigenvalues j ≤ 32 * ρ}) := by sorry

end CubeSampling
