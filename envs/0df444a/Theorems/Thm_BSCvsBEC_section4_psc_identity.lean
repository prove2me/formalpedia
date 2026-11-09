-- Prove2me | Theorems.Thm_BSCvsBEC_section4_psc_identity
-- name    : BSCvsBEC.section4_psc_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:35:07.194044+00:00
-- url     : https://prove2.me/theorems/afb92bbf-f2fd-44fb-8c33-df3569f36eb8
-- title:
--   §4 identity: $H(X\mid \mathrm{PSC}_\theta(X))=H(X)-H(Y)$
-- statement:
--   Let $\Omega$ be a finite alphabet, $d\ge1$, and $(\omega_a)_{a\in\Omega}$ unit vectors in $\mathbb C^d$. For a random $X\in\Omega^n$ with pmf $P$, sent through the channel $x\mapsto|\omega_x\rangle=\bigotimes_i|\omega_{x_i}\rangle$, with joint state $\sigma_{XY}=\sum_xP(x)|x\rangle\langle x|\otimes|\omega_x\rangle\langle\omega_x|$ and output $\sigma_Y$,
--   $$H(X\mid Y)=H(X)-H(Y),$$
--   where $H(X\mid Y)=S(\sigma_{XY})-S(\sigma_Y)$, $H(X)$ is the Shannon entropy of $P$ and $H(Y)=S(\sigma_Y)$ (bits).
--
--   The paper uses this ("because $Y$ is pure conditioned on $X=x$") for $\mathrm{PSC}_\theta$ to turn Theorem 1.3 into the entropy inequality of Theorem 4.1.
--
--   Differences from the source:
--   - generalization: PSC_θ: Ω = F₂, d = 2, ⟨ω₀|ω₁⟩ = cos θ → any finite Ω, any d, any family of unit vectors ω : Ω → ℂ^d; reason: the identity uses only that each channel output is a pure state; Ω = Fin 2, d = 2 and IsPSCPair θ ω give the page's case
--   - encoding: a random variable X on a finite set → its pmf P with IsPMF P; reason: Lean convention; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §4, p.18

import Mathlib
import Definitions.Def_BSCvsBEC_shannon
import Definitions.Def_BSCvsBEC_condEntPSC

namespace BSCvsBEC

/-- **§4, p.18 (PSC identity).** For a random `X ∈ Ωⁿ` with pmf `P` sent through a channel whose
outputs are the pure product states `|ω_x⟩ = ⨂ᵢ |ω_{xᵢ}⟩`, `H(X | Y) = H(X) − H(Y)`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), §4, p.18: "because `Y` is pure conditioned on `X = x`, we have that `H(X | Y) = H(X) − H(Y)`."

**Formalization Note.** Stated for any finite alphabet `Ω`, any dimension `d` and any family of unit
vectors `ω : Ω → ℂ^d` (the page's case is `PSC_θ`: `Ω = F₂`, `d = 2`, `IsPSCPair θ ω`). -/
theorem section4_psc_identity {Ω : Type} [Fintype Ω] [DecidableEq Ω] {d n : ℕ}
    (ω : Ω → EuclideanSpace ℂ (Fin d)) (hω : ∀ a, ‖ω a‖ = 1)
    (P : (Fin n → Ω) → ℝ) (hP : IsPMF P) :
    condEntPSC ω P = shannon P - ShadowTomography.QuantumLB.vnEntropy (outState P (pscVec ω)) := by sorry

end BSCvsBEC
