-- Prove2me | Theorems.Thm_DQIShattered_eq_3_29_3_31
-- name    : DQIShattered.eq_3_29_3_31
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:23.16612+00:00
-- url     : https://prove2.me/theorems/0195724b-ac43-4eff-b7f8-026750986926
-- title:
--   (3.29)–(3.31) — $\hat e<K_*/D\iff\gamma<\gamma_{\mathrm{USD}}$, and $\beta_{\mathrm{ALG}}=\tanh^{-1}(K_*/D)$
-- statement:
--   Let $k\ge3$ and $D\ge k$.
--
--   1. **(3.29)–(3.30).** For $\gamma\in[0,1/2]$,
--   $$2\sqrt{\gamma(1-\gamma)}<\frac{K_*(k)}{D}\iff\gamma<\gamma_{\mathrm{USD}}(k,D)=\frac12-\frac12\sqrt{1-\Big(\frac{K_*(k)}{D}\Big)^2}.$$
--   2. **(3.31).** For $\beta\ge0$ and $\gamma=\frac12-\frac12\operatorname{sech}\beta$ (that is, $\beta=\operatorname{sech}^{-1}(1-2\gamma)$, (2.6)),
--   $$\gamma<\gamma_{\mathrm{USD}}(k,D)\iff\tanh\beta<\frac{K_*(k)}{D},$$
--   so the USD threshold in inverse temperature is $\beta_{\mathrm{ALG}}(k,D)=\tanh^{-1}(K_*(k)/D)$.
--
--   These identities convert the rank threshold into the decodable error rate and then into the inverse temperature of Theorem 2.7.
--
--   Differences from the source:
--   - reading: substituting (3.30) into (2.6) gives β_ALG(k, D) = tanh⁻¹(K_*(k)/D) → for β ≥ 0, gammaOf β < γ_USD(k, D) ↔ tanh β < K_*(k)/D; reason: β ↦ γ(β) and tanh are strictly increasing, so the identity β_ALG = sech⁻¹(1 − 2γ_USD) is this equivalence
--   - encoding: tanh⁻¹, sech⁻¹ → tanh β < K_*(k)/D and γ = 1/2 − 1/(2 cosh β); reason: Mathlib has no sech⁻¹; K_*(k)/D < 1, so both are equivalent rewritings
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), (3.29)–(3.31), p.17

import Mathlib
import Definitions.Def_DQIShattered_Thresholds

namespace DQIShattered

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, (3.29)–(3.31), p.17.

Let `k ≥ 3` and `D ≥ k`.

1. **(3.29)–(3.30).** For `γ ∈ [0, 1/2]`, `2√(γ(1−γ)) < K_*(k)/D` if and only if
   `γ < γ_USD(k, D) = 1/2 − (1/2)√(1 − (K_*(k)/D)²)`.
2. **(3.31).** For `β ≥ 0` and `γ = 1/2 − (1/2) sech β` (the relation (2.6)), `γ < γ_USD(k, D)` if and only if
   `tanh β < K_*(k)/D`, i.e. `β < β_ALG(k, D) = tanh⁻¹(K_*(k)/D)`.

**Formalization Note** `tanh⁻¹` and `sech⁻¹` are avoided: `tanh` is strictly increasing and `K_*(k)/D < 1`, so
`β < tanh⁻¹(K_*(k)/D)` is `tanh β < K_*(k)/D`; `γ = gammaOf β` is `β = sech⁻¹(1 − 2γ)`. -/
theorem eq_3_29_3_31 (k : ℕ) (hk : 3 ≤ k) (D : ℝ) (hD : (k : ℝ) ≤ D) :
    (∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 / 2 → (erasureRate γ < Kstar k / D ↔ γ < gammaUSD k D)) ∧
    ∀ β : ℝ, 0 ≤ β → (gammaOf β < gammaUSD k D ↔ Real.tanh β < Kstar k / D) := by sorry

end DQIShattered
