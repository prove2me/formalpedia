-- Prove2me | Theorems.Thm_DQIShattered_post_processing
-- name    : DQIShattered.post_processing
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:30:26.12104+00:00
-- url     : https://prove2.me/theorems/53a9aff5-3d7c-4c39-a456-6165a95e3d93
-- title:
--   p.10 and p.13 — $\mathcal D_{\mathrm{target}}$ lives on $C$ and $K_B\mathcal D_{\mathrm{target}}=\mu_{\beta,H_{B,J}}$
-- statement:
--   Let $B\in\mathbb F_2^{M\times N}$, $J=(-1)^v$, $\beta\in\mathbb R$, and let $z_0$ be a fixed configuration.
--
--   1. The law $\mathcal D_{\mathrm{target}}(B,J,\beta)$ of a computational-basis measurement of $|\Phi_{\mathrm{target}}\rangle$ is supported on $C=\{Bx\}$ and has total mass $1$.
--   2. The post-processing channel $K_B$ maps it to the Gibbs measure:
--   $$K_B\,\mathcal D_{\mathrm{target}}(B,J,\beta)=\mu_{\beta,H_{B,J}} .$$
--
--   Hence an exact preparation of $|\Phi_{\mathrm{target}}\rangle$ followed by $K_B$ samples the Gibbs measure exactly.
--
--   Differences from the source:
--   - encoding: spin configurations z ∈ {±1}^N and couplings J ∈ {±1}^M → z = (−1)^x, J = (−1)^v with x ∈ 𝔽₂^N, v ∈ 𝔽₂^M; reason: bijections; same instances
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), §3.1, p.10 and proof of Theorem 2.4, p.13

import Mathlib
import Definitions.Def_DQIShattered_DQI

namespace DQIShattered

open Finset

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, §3.1, p.10, and proof of Theorem 2.4, p.13.

For every `B ∈ 𝔽₂^{M×N}`, `J = (−1)^v`, `β ∈ ℝ` and fixed configuration `z₀ = (−1)^{x₀}`:

1. `𝒟_target(B, J, β)` is supported on the code `C = {Bx : x ∈ 𝔽₂^N}` and has total mass `1` (p.10: measuring
   `|Φ_target⟩` returns `y` with probability equal to the total Gibbs weight of its preimages);
2. `K_B 𝒟_target(B, J, β) = µ_{β,H_{B,J}}` (p.13). -/
theorem post_processing {M N : ℕ} (B : Matrix (Fin M) (Fin N) (ZMod 2)) (v : Fin M → ZMod 2) (β : ℝ)
    (x₀ : Fin N → ZMod 2) :
    (∀ y, y ∉ univ.image B.mulVec → Dtarget B v β y = 0) ∧ ∑ y, Dtarget B v β y = 1 ∧
      postProcess B x₀ (Dtarget B v β) = gibbs B v β := by sorry

end DQIShattered
