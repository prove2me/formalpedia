-- Prove2me | Theorems.Thm_DynFairDiv_Uniform_eq_E_1
-- name    : DynFairDiv.Uniform.eq_E_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-19T04:22:01.824003+00:00
-- url     : https://prove2.me/theorems/8b614970-8380-4ac1-9e8e-b3736de64b12
-- title:
--   Display (E.1), p. 959 — S^{ℓ(d+1)} → σ(d+1)ln((d+1)/d) as ℓ → ∞ for FFA on the infinite d-uniform vector
-- statement:
--   Fix $d \ge 1$ and $\sigma \in \mathbb{R}$, and let $S^t$ be the total resource allocated by the frugally fair algorithm with ratio $\sigma$ on the infinite $d$-uniform control vector when $t$ users are present. Along the times $t = \ell(d+1)$,
--   $$\lim_{\ell\to\infty} S^{\ell(d+1)} \;=\; \sigma\,(d+1)\,\ln\!\Big(\frac{d+1}{d}\Big).$$
--
--   Combined with the monotonicity of $S^t$, this identifies the largest $\sigma$ for which FFA stays within the resource on the infinite $d$-uniform vector.
-- source:
--   Vardi, Psomas, Friedman, Dynamic Fair Resource Division, Math. Oper. Res. 47(2):945–968 (2022), p. 959, display (E.1) in the proof of Theorem 4

import Mathlib
import Definitions.Def_DynFairDiv_Uniform_Model

namespace DynFairDiv.Uniform

theorem eq_E_1 (d : ℕ) (hd : 1 ≤ d) (σ : ℝ) :
    Filter.Tendsto (fun ℓ : ℕ => ffaTotal (uniformCV d) σ (ℓ * (d + 1))) Filter.atTop
      (nhds (σ * ((d : ℝ) + 1) * Real.log (((d : ℝ) + 1) / d))) := by sorry

end DynFairDiv.Uniform
