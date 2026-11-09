-- Prove2me | Theorems.Thm_CubeSampling_proposition_5_2
-- name    : CubeSampling.proposition_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:18:23.902934+00:00
-- url     : https://prove2.me/theorems/18ff3bdc-8e07-4889-9d4b-ead7bf244ca3
-- title:
--   Proposition 5.2 — harmonic lift
-- statement:
--   **Proposition 5.2.** Fix $\rho \in (0,1)$ and $q_0 \in (0,1/2)$. There is $C_{\rho,q_0}$ such that for integers $d, k, R$ with $1 \le k \le q_0 d$ and $0 \le R \le k$ there are a subspace $W_{\le R} \subseteq P_{d,k}$ of dimension $\binom dR$ and a permutation-invariant set $E$ such that, with $K = k - R$,
--   $$
--   \mu_d(E) \le e^{-E_{d,k}(R) + C_{\rho,q_0}K^{1/3}}, \qquad \mathbb E[h^2\mathbf 1_{E^c}] \le \rho\,\mathbb E[h^2] \quad (h \in W_{\le R}).
--   $$
--   Consequently,
--   $$
--   \mu_d(E) \le e^{-\Lambda_{d,k} + C_{\rho,q_0}(R + k^{1/3})}. \tag{14}
--   $$
--   Here $E_{d,k}(R) = d\,I(\tau_R/d)$, $\tau_R = 2\sqrt{(k-R)(d-k-R)}$ and $I(z) = \log 2 - H_2((1-z)/2)$.
--
--   Differences from the source: none.
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Proposition 5.2, (14), p.20

import Mathlib
import Definitions.Def_CubeSampling_lowDeg
import Definitions.Def_CubeSampling_IsPermInvariant
import Definitions.Def_CubeSampling_cubeProb
import Definitions.Def_CubeSampling_outsideEnergy
import Definitions.Def_CubeSampling_Edk
import Definitions.Def_CubeSampling_Lambda

namespace CubeSampling

/-- Proposition 5.2 (harmonic lift) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Proposition 5.2, (14), p.20): fix `ρ ∈ (0, 1)` and
`q₀ ∈ (0, 1/2)`. For integers `d, k, R` with `1 ≤ k ≤ q₀ d` and `0 ≤ R ≤ k` there are `W_{≤R} ⊆ P_{d,k}` of
dimension `C(d, R)` and a permutation-invariant `E` such that, with `K = k − R`,
`μ_d(E) ≤ e^{−E_{d,k}(R) + C_{ρ,q₀} K^{1/3}}` and `E[h² 1_{E^c}] ≤ ρ E[h²]` for `h ∈ W_{≤R}`; consequently
(14) `μ_d(E) ≤ e^{−Λ_{d,k} + C_{ρ,q₀}(R + k^{1/3})}`.

**Formalization Note** One constant `C_{ρ,q₀}` for both probability bounds. -/
theorem proposition_5_2 (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1) (q₀ : ℝ) (hq₀ : 0 < q₀)
    (hq₀' : q₀ < 1 / 2) :
    ∃ C : ℝ, ∀ d k R : ℕ, 1 ≤ k → (k : ℝ) ≤ q₀ * d → R ≤ k →
      ∃ W : Submodule ℝ (Cube d → ℝ), W ≤ lowDeg d k ∧ Module.finrank ℝ W = d.choose R ∧
      ∃ E : Set (Cube d), IsPermInvariant E ∧
        cubeProb d E ≤ Real.exp (-Edk d k R + C * ((k : ℝ) - R) ^ ((1 : ℝ) / 3)) ∧
        (∀ h ∈ W, outsideEnergy d E h ≤ ρ * cubeMean d (fun x => h x ^ 2)) ∧
        cubeProb d E ≤ Real.exp (-Lambda d k + C * ((R : ℝ) + (k : ℝ) ^ ((1 : ℝ) / 3))) := by sorry

end CubeSampling
