-- Prove2me | Theorems.Thm_DQIShattered_eq_3_7_3_10
-- name    : DQIShattered.eq_3_7_3_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:30:12.581494+00:00
-- url     : https://prove2.me/theorems/eadc39d4-87f3-4981-b528-0e63ced5a731
-- title:
--   (3.7), (3.9), (3.10) — $H^{\otimes M}|\Phi_{\mathrm{target}}\rangle\propto\sum_{d\in C^\perp}\sum_e(-1)^{v\cdot e}\hat F(e)|d+e\rangle$
-- statement:
--   Let $B\in\mathbb F_2^{M\times N}$, $J=(-1)^v$ and $\beta\ge0$. The Hadamard transform of the target state (3.2) is a positive multiple of
--
--   $$|\hat\Phi_{\mathrm{target}}\rangle=\sum_{d\in C^\perp}\sum_{e\in\mathbb F_2^M}(-1)^{v\cdot e}\,\hat F(e)\,|d+e\rangle,\qquad \hat F(e)=\sqrt{1-\gamma}^{\,M-|e|}\sqrt\gamma^{\,|e|},\qquad \gamma=\frac12-\frac12\operatorname{sech}\beta .$$
--
--   That is, $H^{\otimes M}|\Phi_{\mathrm{target}}\rangle=c\,|\hat\Phi_{\mathrm{target}}\rangle$ for some real $c>0$.
--
--   This identity is what lets DQI prepare the Gibbs state from a quantum decoder at error rate $\gamma$. It is the origin of the relation (2.6) between $\beta$ and $\gamma$.
--
--   Differences from the source:
--   - reading: (3.9)–(3.10) for the inverse temperature β → β ≥ 0; reason: β = sech⁻¹(1 − 2γ) ≥ 0 throughout §3.1; for β < 0 the transform of F carries the sign (−1)^{|e|}
--   - encoding: F̂(e) ∝ √(1−γ)^{M−|e|} √γ^{|e|} → H^{⊗M}|Φ_target⟩ = c·|Φ̂_target⟩ with an existential real c > 0; reason: the page leaves the constant implicit
--   - encoding: Hadamard transform → entries 2^{−M/2}(−1)^{y·r}; reason: the standard H^{⊗M}
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), (3.7), (3.9), (3.10), pp.10–11

import Mathlib
import Definitions.Def_DQIShattered_DQI

namespace DQIShattered

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, (3.7), (3.9), (3.10), pp.10–11.

For every `B ∈ 𝔽₂^{M×N}`, every `J = (−1)^v` and every `β ≥ 0`, the Hadamard transform of the target state is
proportional, with a positive constant, to
`|Φ̂_target⟩ = ∑_{d ∈ C^⊥} ∑_{e ∈ 𝔽₂^M} (−1)^{v·e} F̂(e) |d + e⟩`, where `F̂(e) = √(1−γ)^{M−|e|} √γ^{|e|}` and
`γ = 1/2 − (1/2) sech β`:
`H^{⊗M}|Φ_target⟩ = c |Φ̂_target⟩` for some `c > 0`.

**Formalization Note** The page writes `F̂(e) ∝ …`; the constant is kept as an existential `c > 0`. `H^{⊗M}` has
entries `2^{−M/2}(−1)^{y·r}`. -/
theorem eq_3_7_3_10 {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2) (β : ℝ)
    (hβ : 0 ≤ β) :
    ∃ c : ℝ, 0 < c ∧ hadamardT (phiTarget B v β) = fun y => (c : ℂ) * phiHatTarget B v β y := by sorry

end DQIShattered
