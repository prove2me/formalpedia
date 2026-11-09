-- Prove2me | Theorems.Thm_CubeSampling_lemma_4_3
-- name    : CubeSampling.lemma_4_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:19:00.571359+00:00
-- url     : https://prove2.me/theorems/82fc69a6-34cf-435f-a63e-6874b8960178
-- title:
--   Lemma 4.3 — one-dimensional concentration witness
-- statement:
--   **Lemma 4.3.** Fix $\rho \in (0,1)$ and $q_0 \in (0,1/2)$. There are constants $M_{\rho,q_0}, C_{\rho,q_0} > 0$ and $L_0$ such that for all integers $\ell \ge L_0$ and $D$ with $\ell \le q_0 D$ there is a unit radial polynomial $p$ on $\{-1,1\}^D$ of exact degree $\ell$ for which the cutoff
--   $$
--   \tau = 2\sqrt{\ell(D-\ell)}, \qquad u = \tau - M_{\rho,q_0}\sqrt D\,\ell^{-1/6} > 0
--   $$
--   satisfies
--   $$
--   \mathbb E\bigl[p^2\mathbf 1\{S_D < u\}\bigr] \le \rho, \qquad \mu_D(S_D \ge u) \le \exp\bigl\{-D\Psi(\ell/D) + C_{\rho,q_0}\ell^{1/3}\bigr\}.
--   $$
--
--   It provides the radial factors of the harmonic lift (Proposition 5.2) and the lower bound in Proposition 3.3.
--
--   Differences from the source:
--   - encoding: for all sufficiently large ℓ ≤ q₀D → ∃ L₀, ∀ ℓ ≥ L₀ with ℓ ≤ q₀D; reason: the threshold depends only on ρ and q₀, like the constants
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Lemma 4.3, p.18

import Mathlib
import Definitions.Def_CubeSampling_IsRadial
import Definitions.Def_CubeSampling_HasExactDegree
import Definitions.Def_CubeSampling_cubeMean
import Definitions.Def_CubeSampling_coordSum
import Definitions.Def_CubeSampling_outsideEnergy
import Definitions.Def_CubeSampling_cubeProb
import Definitions.Def_CubeSampling_Psi

namespace CubeSampling

/-- Lemma 4.3 (one-dimensional concentration witness) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Lemma 4.3, p.18): fix `ρ ∈ (0, 1)` and
`q₀ ∈ (0, 1/2)`. There are constants `M_{ρ,q₀}, C_{ρ,q₀} > 0` such that, for all sufficiently large
`ℓ ≤ q₀ D`, there is a unit radial polynomial `p` of exact degree `ℓ` for which the cutoff
`τ = 2√(ℓ(D − ℓ))`, `u = τ − M_{ρ,q₀} √D ℓ^{−1/6} > 0` satisfies `E[p² 1{S_D < u}] ≤ ρ` and
`μ_D(S_D ≥ u) ≤ exp{−DΨ(ℓ/D) + C_{ρ,q₀} ℓ^{1/3}}`.

**Formalization Note** `E[p² 1{S_D < u}]` is `outsideEnergy` of the ball `{S_D ≥ u}`; "sufficiently
large" is `∃ L₀, ∀ ℓ ≥ L₀`. -/
theorem lemma_4_3 (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1) (q₀ : ℝ) (hq₀ : 0 < q₀) (hq₀' : q₀ < 1 / 2) :
    ∃ M C : ℝ, 0 < M ∧ 0 < C ∧ ∃ L₀ : ℕ, ∀ D ℓ : ℕ, L₀ ≤ ℓ → (ℓ : ℝ) ≤ q₀ * D →
      ∃ p : Cube D → ℝ, IsRadial D p ∧ cubeMean D (fun x => p x ^ 2) = 1 ∧ HasExactDegree D ℓ p ∧
        let τ : ℝ := 2 * Real.sqrt ((ℓ : ℝ) * ((D : ℝ) - ℓ))
        let u : ℝ := τ - M * Real.sqrt D * (ℓ : ℝ) ^ (-(1 : ℝ) / 6)
        0 < u ∧ outsideEnergy D {x | u ≤ (coordSum D x : ℝ)} p ≤ ρ ∧
          cubeProb D {x | u ≤ (coordSum D x : ℝ)} ≤
            Real.exp (-((D : ℝ) * Psi ((ℓ : ℝ) / D)) + C * (ℓ : ℝ) ^ ((1 : ℝ) / 3)) := by sorry

end CubeSampling
