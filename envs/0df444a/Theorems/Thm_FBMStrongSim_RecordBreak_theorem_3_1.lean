-- Prove2me | Theorems.Thm_FBMStrongSim_RecordBreak_theorem_3_1
-- name    : FBMStrongSim.RecordBreak.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:01:41.08866+00:00
-- url     : https://prove2.me/theorems/7416a95f-7ae9-4a39-9fa5-b82bcbf5c3ce
-- title:
--   Theorem 3.1, p. 8 — for k > K(ν), P(max_j |a^k_j − b^k_j| ≥ ρℓ_k) ≤ 2exp{−ν*²·2^{2kδ−2}}, ρ = 2(ν + ν*)
-- statement:
--   Let $B$ be a fractional Brownian motion on $[0,1]$ with Hurst index $H\in(0,1)$, fix $\delta\in(0,H)$, and put $\ell_k=2^{-(H-\delta)k}$ and $K(\nu)=\sup\{n\ge1:4\sqrt n>\nu\cdot2^{\delta n}\}$. For all constants $\nu,\nu^*>0$ and all $k>K(\nu)$,
--   $$\mathbb P\Big(\max_{0\le j\le 2^{k-1}-1}|a^k_j-b^k_j|\ge\rho\,\ell_k\Big)\le 2\exp\big\{-\nu^{*2}\cdot 2^{2k\delta-2}\big\},\qquad \rho=2(\nu+\nu^*),$$
--   where $a^k_j$, $b^k_j$ are the midpoint displacement quantities (3.1).
--
--   This super-exponential tail bound on the level-$k$ increment is the engine of the paper: it makes record-breaking levels summable (Theorem 3.5) and gives every exponential moment of the last record level (Theorem 3.6).
--
--   **Formalization Note** The paper's first equality $\mathbb P(\|B^H_k-B^H_{k-1}\|_\infty\ge\rho\ell_k)=\mathbb P(\max_j|a^k_j-b^k_j|\ge\rho\ell_k)$ is the deterministic identity of the companion milestone (display after (3.1)) and is not repeated here.
-- source:
--   Chen, Dong & Ni, ε-Strong simulation of fractional Brownian motion and related stochastic differential equations, arXiv:1902.07824v1, p. 8, Theorem 3.1 (proof pp. 9–11)

import Mathlib
import Definitions.Def_FBMStrongSim_RecordBreak_Model

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace FBMStrongSim.RecordBreak

/-- Theorem 3.1, p. 8: for `ν, ν* > 0`, `ρ = 2(ν + ν*)` and every `k > K(ν)`,
`P(max_j |a^k_j − b^k_j| ≥ ρ ℓ_k) ≤ 2 exp{−ν*² · 2^{2kδ−2}}`. -/
theorem theorem_3_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {H delta : ℝ} (hH0 : 0 < H) (hH1 : H < 1) (hdelta0 : 0 < delta) (hdeltaH : delta < H)
    {B : ℝ → Ω → ℝ} (hB : IsFBM H B P)
    {nu nuStar : ℝ} (hnu : 0 < nu) (hnuStar : 0 < nuStar) {k : ℕ} (hk : Knu nu delta < k) :
    P {ω | 2 * (nu + nuStar) * ell H delta k ≤ maxDisp (fun s => B s ω) k}
      ≤ ENNReal.ofReal (2 * Real.exp (-nuStar ^ 2 * (2 : ℝ) ^ (2 * (k : ℝ) * delta - 2))) := by sorry

end FBMStrongSim.RecordBreak
