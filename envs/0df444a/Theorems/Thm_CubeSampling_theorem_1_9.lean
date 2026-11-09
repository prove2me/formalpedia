-- Prove2me | Theorems.Thm_CubeSampling_theorem_1_9
-- name    : CubeSampling.theorem_1_9
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T12:18:39.477548+00:00
-- url     : https://prove2.me/theorems/245262a1-7a59-46da-bd42-2be1bd1a2ce6
-- title:
--   Theorem 1.9 — subspace uncertainty principle
-- statement:
--   **Theorem 1.9.** Fix $q_0 \in (0,1/2)$ and $\rho \in (0,1)$. There is $C_{\rho,q_0}$ such that for all integers $1 \le k \le q_0 d$:
--
--   1. For every set $E \subseteq \{-1,1\}^d$, if some nonzero $h \in P_{d,k}$ satisfies $\mathbb E[h^2\mathbf 1_{E^c}] \le \rho\,\mathbb E[h^2]$, then
--   $$
--   \mu_d(E) \ge \exp\{-\Lambda_{d,k} - C_{\rho,q_0}k^{1/3}\}.
--   $$
--   2. Conversely, there exist a subspace $W \subseteq P_{d,k}$ of dimension $M_{d,k}$ and a permutation-invariant set $E$ such that
--   $$
--   \mu_d(E) \le \exp\{-\Lambda_{d,k} + C_{\rho,q_0}k^{1/3}\}, \qquad \mathbb E[h^2\mathbf 1_{E^c}] \le \rho\,\mathbb E[h^2] \ \ \forall h \in W .
--   $$
--   3. For sufficiently large $k$ (that is, $k \ge K_0(\rho, q_0)$), the set $E$ in 2 is a Hamming ball.
--
--   The converse supplies the hard subspaces for the lower bound in Theorem 1.5.
--
--   Differences from the source:
--   - reading: For sufficiently large k, E is a Hamming ball → ∃ K₀ (depending on ρ, q₀): k ≥ K₀ → the E of the converse is a Hamming ball; reason: Remark 5.3 (p.21): for large k the construction is E = {S_d ≥ u}, a Hamming ball, with the stated properties
-- source:
--   Weinberger, Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube, arXiv:2610.12358 (version of 2 Nov 2026), Theorem 1.9, p.6

import Mathlib
import Definitions.Def_CubeSampling_lowDeg
import Definitions.Def_CubeSampling_IsPermInvariant
import Definitions.Def_CubeSampling_IsHammingBall
import Definitions.Def_CubeSampling_cubeProb
import Definitions.Def_CubeSampling_outsideEnergy
import Definitions.Def_CubeSampling_Lambda
import Definitions.Def_CubeSampling_Mdk

namespace CubeSampling

/-- Theorem 1.9 (subspace uncertainty principle) (Weinberger, *Subspace Uncertainty and Sharp Sampling Thresholds on the Boolean Cube*, arXiv:2610.12358 (version of 2 Nov 2026, sha256 43fdcd90…4f79), Theorem 1.9, p.6): fix `q₀ ∈ (0, 1/2)`,
`ρ ∈ (0, 1)` and integers `1 ≤ k ≤ q₀ d`. For every set `E`, if some nonzero `h ∈ P_{d,k}` satisfies
`E[h² 1_{E^c}] ≤ ρ E[h²]`, then `μ_d(E) ≥ exp{−Λ_{d,k} − C_{ρ,q₀} k^{1/3}}`. Conversely, there exist
`W ⊆ P_{d,k}` of dimension `M_{d,k}` and a permutation-invariant set `E` with
`μ_d(E) ≤ exp{−Λ_{d,k} + C_{ρ,q₀} k^{1/3}}` and `E[h² 1_{E^c}] ≤ ρ E[h²]` for all `h ∈ W`. For sufficiently
large `k`, `E` is a Hamming ball.

**Formalization Note** "For sufficiently large `k`" is `∃ K₀` (depending on `ρ, q₀`) such that for
`k ≥ K₀` the set `E` of the converse can be chosen a Hamming ball. -/
theorem theorem_1_9 (q₀ : ℝ) (hq₀ : 0 < q₀) (hq₀' : q₀ < 1 / 2) (ρ : ℝ) (hρ : 0 < ρ) (hρ' : ρ < 1) :
    ∃ C : ℝ, ∃ K₀ : ℕ, ∀ d k : ℕ, 1 ≤ k → (k : ℝ) ≤ q₀ * d →
      (∀ (E : Set (Cube d)) (h : Cube d → ℝ), h ∈ lowDeg d k → h ≠ 0 →
          outsideEnergy d E h ≤ ρ * cubeMean d (fun x => h x ^ 2) →
          Real.exp (-Lambda d k - C * (k : ℝ) ^ ((1 : ℝ) / 3)) ≤ cubeProb d E) ∧
      (∃ W : Submodule ℝ (Cube d → ℝ), W ≤ lowDeg d k ∧ Module.finrank ℝ W = Mdk d k ∧
        ∃ E : Set (Cube d), IsPermInvariant E ∧
          cubeProb d E ≤ Real.exp (-Lambda d k + C * (k : ℝ) ^ ((1 : ℝ) / 3)) ∧
          (∀ h ∈ W, outsideEnergy d E h ≤ ρ * cubeMean d (fun x => h x ^ 2)) ∧
          (K₀ ≤ k → IsHammingBall E)) := by sorry

end CubeSampling
