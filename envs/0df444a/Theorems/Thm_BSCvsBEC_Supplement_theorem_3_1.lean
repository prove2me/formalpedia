-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_3_1
-- name    : BSCvsBEC.Supplement.theorem_3_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:37:48.979689+00:00
-- url     : https://prove2.me/theorems/2c7af628-83d2-44fc-aa52-e26e3a8ee5af
-- title:
--   Theorem 3.1 — $P_e(\mathrm{PSC}_\theta,X)\le P_e(\mathrm{BEC}_\lambda,X)$ for $\lambda\ge\cos^2\theta$
-- statement:
--   Let $X\in\mathbb F_2^n$ be a random variable (for example uniform on a code $\mathcal C$) and let $0\le\theta\le\pi/2$. Let $|\omega_0\rangle,|\omega_1\rangle\in\mathbb C^2$ be unit vectors with $\langle\omega_0|\omega_1\rangle=\cos\theta$. Then
--   $$P_e(\mathrm{PSC}_\theta,X)\ \le\ P_e(\mathrm{BEC}_\lambda,X)\qquad\text{provided }\lambda\ge\cos^2\theta,$$
--   where $P_e=1-P_{\mathrm{guess}}$ is the error probability of optimal decoding: the best POVM on the output states $|\omega_x\rangle\langle\omega_x|$ for the pure state channel, MAP decoding for the erasure channel.
--
--   The constant $\cos^2\theta$ cannot be lowered, already for $n=1$; the trivial degradation of $\mathrm{PSC}_\theta$ to $\mathrm{BEC}_{\cos\theta}$ gives only $\lambda\ge\cos\theta$.
--
--   Differences from the source:
--   - reading: some fixed pure states |ω₀⟩, |ω₁⟩ with ⟨ω₀|ω₁⟩ = cos θ → every pair of unit vectors in ℂ² with inner ω₀ ω₁ = cos θ (IsPSCPair θ ω); reason: the page fixes an arbitrary such pair; the statement is required for each one
--   - encoding: a random variable X on a finite set → its pmf P with IsPMF P; reason: Lean convention; same instances
--   - encoding: provided λ ≥ cos²θ → cos²θ ≤ λ ≤ 1; reason: λ is the erasure probability of BEC_λ, defined only for λ ∈ [0, 1]
--   - encoding: P_guess as max over POVMs (eq. (17)) → sSup over every POVM indexed by the input alphabet (pGuess); reason: the set of values is nonempty and bounded above by 1 for a pmf and density matrices, so the supremum is the maximum's value
--   - encoding: MAP decoding on BEC_λ → pGuess of the diagonal cq states becState λ x = diag(∏ᵢ W(yᵢ|xᵢ)); reason: the page's eq. (17) treats a classical channel as a cq channel with diagonal states; the optimal POVM value equals MAP decoding
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 3.1, eq. (64), p.13; P_e, P_guess: eqs. (16)–(17), p.6

import Mathlib
import Definitions.Def_BSCvsBEC_shannon
import Definitions.Def_BSCvsBEC_condEntPSC
import Definitions.Def_BSCvsBEC_Supplement_pErr

namespace BSCvsBEC.Supplement

/-- **Theorem 3.1 (p.13).** Let `X ∈ F₂ⁿ` be a random variable (e.g., uniform on a code `𝒞`) and let
`0 ≤ θ ≤ π/2`. Then `P_e(PSC_θ, X) ≤ P_e(BEC_λ, X)` provided `λ ≥ cos²θ` (eq. (64)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 3.1, eq. (64), p.13; `P_e` as in eqs. (16)–(17), p.6.

**Formalization Note.** `X` has pmf `P` on `Fin n → Fin 2`. On the PSC side the output states are
`|ω_x⟩⟨ω_x|` (`ketbra (pscVec ω x)`) for any pair `ω` with `IsPSCPair θ ω`; on the BEC side they are the
diagonal states `becState λ x`, so its `P_guess` is MAP decoding. `P_e = 1 − P_guess` with `P_guess`
the supremum over all POVMs. `λ` ranges over `[cos²θ, 1]` (`λ ≤ 1`: an erasure probability). -/
theorem theorem_3_1 (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ Real.pi / 2)
    (ω : Fin 2 → EuclideanSpace ℂ (Fin 2)) (hω : BSCvsBEC.IsPSCPair θ ω)
    (n : ℕ) (P : (Fin n → Fin 2) → ℝ) (hP : BSCvsBEC.IsPMF P)
    (lam : ℝ) (hl : Real.cos θ ^ 2 ≤ lam) (hl1 : lam ≤ 1) :
    pErr P (fun x => BSCvsBEC.ketbra (BSCvsBEC.pscVec ω x)) ≤ pErr P (becState lam) := by sorry

end BSCvsBEC.Supplement
