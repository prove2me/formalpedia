-- Prove2me | Theorems.Thm_ClonableQMASep_Main_lemma_2
-- name    : ClonableQMASep.Main.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T21:24:22.977959+00:00
-- url     : https://prove2.me/theorems/2395e650-d2b6-4846-a410-fee841eeda9b
-- title:
--   Lemma 2 — Hybrid bound for quantum channels
-- statement:
--   Let $\Phi_1,\dots,\Phi_T$ and $\tilde\Phi_1,\dots,\tilde\Phi_T$ be quantum channels, and let $\Psi_1,\dots,\Psi_T$ be arbitrary quantum channels (including measurements) interleaved after them. Let $\rho_0=\tilde\rho_0$ be a fixed initial density operator and
--   $$\rho_t=\Psi_t(\Phi_t(\rho_{t-1})),\qquad\tilde\rho_t=\Psi_t(\tilde\Phi_t(\tilde\rho_{t-1})).$$
--   If $D\big(\Phi_t(\tilde\rho_{t-1}),\tilde\Phi_t(\tilde\rho_{t-1})\big)\le\epsilon_t$ for every $t$, then
--   $$D(\rho_T,\tilde\rho_T)\le\sum_{t=1}^T\epsilon_t .$$
--   With every $\Psi_t$ the identity this is the basic statement $\rho_t=\Phi_t(\rho_{t-1})$.
--
--   It is used in Lemma 6 to add up the errors of the $nR$ hash-extraction calls of the cloning algorithm.
--
--   Differences from the source:
--
--   - encoding: the basic statement and its interleaved variant (last sentence) → one statement with channels Ψ_t after each Φ_t, Φ̃_t; Ψ_t = id gives the basic statement; reason: the source asserts both; the interleaved one contains the basic one
--   - encoding: quantum channels; D(ρ, σ) = ½‖ρ − σ‖₁ → Kraus-form maps between finite matrix spaces (dimensions may change with t); trace norm as the sum of singular values; reason: finite-dimensional CPTP maps are exactly the Kraus-form maps
--   - encoding: steps t = 1, …, T → steps t = 0, …, T − 1; reason: 0-based index
-- source:
--   Alper Cakan, Kai-Min Chung, Wei-Hsiang Hung, Tzu-Yi Yang, Separating ClonableQMA and QCMA Relative to a Classical Oracle, STOC 2027 submission #844 (October 2026), Lemma 2, pp. 11–12 (including its last sentence on interleaved channels)

import Definitions.Def_ClonableQMASep_Main_Channels

set_option autoImplicit false

namespace ClonableQMASep.Main

/-- Lemma 2 (Hybrid Bound for Quantum Channels, pp. 11–12), interleaved form. Let `Φ_t`, `Φ̃_t`
(`t < T`) be quantum channels and `Ψ_t` arbitrary quantum channels interleaved after them, let
`ρ_0 = ρ̃_0` be a fixed density operator, `ρ_{t+1} = Ψ_t(Φ_t(ρ_t))` and
`ρ̃_{t+1} = Ψ_t(Φ̃_t(ρ̃_t))`. If `D(Φ_t(ρ̃_t), Φ̃_t(ρ̃_t)) ≤ ε_t` for every `t < T`, then
`D(ρ_T, ρ̃_T) ≤ ∑_{t<T} ε_t`. (With `Ψ_t = id` this is the basic form.) -/
theorem lemma_2 (T : ℕ) (d e : ℕ → Type) [∀ t, Fintype (d t)] [∀ t, DecidableEq (d t)]
    [∀ t, Fintype (e t)] [∀ t, DecidableEq (e t)]
    (Φ Φt : ∀ t, Matrix (d t) (d t) ℂ → Matrix (e t) (e t) ℂ)
    (Ψ : ∀ t, Matrix (e t) (e t) ℂ → Matrix (d (t + 1)) (d (t + 1)) ℂ)
    (hΦ : ∀ t, IsChannel (Φ t)) (hΦt : ∀ t, IsChannel (Φt t)) (hΨ : ∀ t, IsChannel (Ψ t))
    (ρ₀ : Matrix (d 0) (d 0) ℂ) (hρ₀ : IsDensity ρ₀) (ε : ℕ → ℝ)
    (hε : ∀ t, t < T →
      traceDist (Φ t (chainState Φt Ψ ρ₀ t)) (Φt t (chainState Φt Ψ ρ₀ t)) ≤ ε t) :
    traceDist (chainState Φ Ψ ρ₀ T) (chainState Φt Ψ ρ₀ T) ≤ ∑ t ∈ Finset.range T, ε t := by sorry

end ClonableQMASep.Main
