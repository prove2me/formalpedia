-- Prove2me | Theorems.Thm_DQIShattered_eq_3_20_3_21
-- name    : DQIShattered.eq_3_20_3_21
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T20:29:22.465336+00:00
-- url     : https://prove2.me/theorems/12655e75-eeda-462f-b7da-e66d33fe07f8
-- title:
--   (3.20)–(3.21) — optimal USD has $p_\perp=|\langle\psi_0|\psi_1\rangle|$; erasure rate $\hat e=2\sqrt{\gamma(1-\gamma)}$
-- statement:
--   **(3.20).** Let $|\psi_0\rangle,|\psi_1\rangle$ be non-orthogonal unit vectors of a finite-dimensional space. Under uniform priors, the optimal unambiguous state discrimination measurement has $\perp$ probability
--
--   $$p_\perp=|\langle\psi_0|\psi_1\rangle| .$$
--
--   Some USD measurement attains this value, and every USD measurement has $p_\perp\ge|\langle\psi_0|\psi_1\rangle|$.
--
--   **(3.21).** Let $\gamma\in[0,1/2]$. Then $|\langle\psi_{0,\gamma}|\psi_{1,\gamma}\rangle|=\hat e=2\sqrt{\gamma(1-\gamma)}$. Moreover, some USD measurement for $|\psi_{0,\gamma}\rangle,|\psi_{1,\gamma}\rangle$ returns $\perp$ with probability exactly $\hat e$ on each of the two states.
--
--   Applying such a measurement qubit by qubit therefore turns the classical-quantum channel (3.19) into a binary erasure channel with erasure probability $\hat e$. This is the channel the USD decoder works with.
--
--   Differences from the source:
--   - encoding: two non-orthogonal states → unit amplitude vectors ψ₀, ψ₁ : ι → ℂ on a finite basis ι with ⟨ψ₀|ψ₁⟩ ≠ 0; reason: all states of the paper are finite-dimensional; same instances
--   - reading: the optimal USD measurement achieves p_⊥ = |⟨ψ₀|ψ₁⟩| → some USD POVM has p_⊥ = |⟨ψ₀|ψ₁⟩|, and every USD POVM has p_⊥ ≥ |⟨ψ₀|ψ₁⟩|; reason: "optimal … achieves" asserts both attainment and optimality
--   - reading: one obtains a classical erasure channel with bit erasure probability ê = 2√(γ(1−γ)) → |⟨ψ_{0,γ}|ψ_{1,γ}⟩| = ê, and some USD POVM has ⊥ probability exactly ê on each of ψ_{0,γ}, ψ_{1,γ}; reason: an erasure channel erases with the same probability whatever the input bit
-- source:
--   Zhou, Shutty, Sellke, Jordan, Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry, arXiv:2609.40345 (held version sha256 0c7f6fdf…), (3.20)–(3.21), p.14

import Mathlib
import Definitions.Def_DQIShattered_Decoding
import Definitions.Def_DQIShattered_Thresholds

namespace DQIShattered

/-- Zhou, Shutty, Sellke, Jordan, *Gibbs Sampling in the Shattered Phase by Decoded Quantum Interferometry*,
arXiv:2609.40345, held version sha256 0c7f6fdf…, (3.20)–(3.21), p.14.

**(3.20).** For two non-orthogonal unit vectors `ψ₀, ψ₁` of a finite-dimensional space, the optimal
unambiguous state discrimination measurement under uniform priors has `⊥` probability `p_⊥ = |⟨ψ₀|ψ₁⟩|`: some
USD measurement attains it, and every USD measurement has `p_⊥ ≥ |⟨ψ₀|ψ₁⟩|`.

**(3.21).** For `γ ∈ [0, 1/2]` and the states `|ψ_{0,γ}⟩, |ψ_{1,γ}⟩` of (2.3), `|⟨ψ_{0,γ}|ψ_{1,γ}⟩| = 2√(γ(1−γ)) = ê`, and
some USD measurement erases each of the two states with probability exactly `ê` (the erasure channel).

**Formalization Note** Vectors are amplitude functions `ι → ℂ` on a finite basis; "optimal achieves" is read as
both attainment and the lower bound. The erasure clause asks `⟨ψ_{b,γ}|E_⊥|ψ_{b,γ}⟩ = ê` for each `b`, which is what
makes the USD output an erasure channel with erasure probability `ê` independent of the input bit. -/
theorem eq_3_20_3_21 :
    (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (ψ₀ ψ₁ : ι → ℂ), IsUnit' ψ₀ → IsUnit' ψ₁ → ip ψ₀ ψ₁ ≠ 0 →
      (∃ E : Option Bool → Matrix ι ι ℂ, IsUSD ψ₀ ψ₁ E ∧ pPerp ψ₀ ψ₁ E = ‖ip ψ₀ ψ₁‖) ∧
        ∀ E : Option Bool → Matrix ι ι ℂ, IsUSD ψ₀ ψ₁ E → ‖ip ψ₀ ψ₁‖ ≤ pPerp ψ₀ ψ₁ E) ∧
    ∀ γ : ℝ, 0 ≤ γ → γ ≤ 1 / 2 →
      ‖ip (qubitState 0 γ) (qubitState 1 γ)‖ = erasureRate γ ∧
        ∃ E : Option Bool → Matrix (ZMod 2) (ZMod 2) ℂ, IsUSD (qubitState 0 γ) (qubitState 1 γ) E ∧
          (expect (E none) (qubitState 0 γ)).re = erasureRate γ ∧
          (expect (E none) (qubitState 1 γ)).re = erasureRate γ := by sorry

end DQIShattered
