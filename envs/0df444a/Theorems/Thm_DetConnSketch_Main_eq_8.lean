-- Prove2me | Theorems.Thm_DetConnSketch_Main_eq_8
-- name    : DetConnSketch.Main.eq_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T06:43:15.176193+00:00
-- url     : https://prove2.me/theorems/664588fd-b11d-4659-801e-fbfef6f07952
-- title:
--   §8.2.5–8.2.6, Eq. (8) — $\lambda_\ell(\tan\theta)=(\cos\theta)^{-m}\varphi_{S_\ell}(\theta)$; positive $\varphi_S(\theta)$ make $M$ positive definite
-- statement:
--   Let $k \ge 1$, $m = k^2$, $\theta \in (0, \pi/2)$, and set $p = \sin\theta$, so that $z = p/\sqrt{1-p^2} = \tan\theta$. Then:
--
--   (i) for every $\ell \in \mathbb F_2^m$, with $S_\ell$ the sign matrix $(S_\ell)_{ij} = (-1)^{\ell_{ij}}$,
--   $$\lambda_\ell(\tan\theta) = (\cos\theta)^{-m}\,\varphi_{S_\ell}(\theta); \tag{8}$$
--
--   (ii) if $\varphi_S(\theta) > 0$ for every sign matrix $S \in \{-1,1\}^{k\times k}$, then the matrix $M$ of Eq. (4) with $p = \sin\theta$ is positive definite.
--
--   Here $\lambda_\ell$ is the polynomial of Eq. (7) and $\varphi_S$ the characteristic function of §8.1. Clause (ii) is how Theorem 8.2 enters the proof of Theorem 8.1.
--
--   Differences from the source:
--   - reading: the displayed identity (8) and the closing sentence of §8.2.6 → one theorem with two clauses for every k ≥ 1 and θ ∈ (0, π/2): (i) the identity for every ℓ, (ii) all φ_S(θ) > 0 ⇒ (lowerBoundMatrix k (sin θ)).PosDef; reason: the section's conclusion; the congruence with A and the character eigenbasis are its proof
--   - encoding: φ_S real-valued (§8.2) / complex-valued (§8.1) → charFun : ℂ; identity (i) in ℂ with λ cast; hypothesis 0 < φ_S(θ) in ℂ's order (real and positive); reason: φ_S is defined as a complex average; the paper shows it is real
--   - encoding: (cos θ)^{−m} → ((cos θ)^{k²})⁻¹; reason: m = k²
-- source:
--   Khanna, Putterman, Sudan, Deterministic Connectivity Sketches Under Edge Deletions, arXiv:2611.06626 (copy sha256 fff87f5b…), pp. 53–55 (PDF 57–59), §8.2.5–8.2.6, Eq. (8)

import Mathlib
import Definitions.Def_DetConnSketch_Main_Signs
import Definitions.Def_DetConnSketch_Main_CharFun
import Definitions.Def_DetConnSketch_Main_TwoLift
import Definitions.Def_DetConnSketch_Main_LowerBoundMatrix

open scoped ComplexOrder

namespace DetConnSketch.Main

/-- §8.2.5–8.2.6, Eq. (8): for `k ≥ 1`, `θ ∈ (0, π/2)` and `p = sin θ` (so `z = tan θ`),
(i) every eigenvalue polynomial satisfies `λ_ℓ(tan θ) = (cos θ)^{−m} φ_{S_ℓ}(θ)` with `m = k²`
(in particular `φ_{S_ℓ}(θ)` is real); (ii) if `φ_S(θ) > 0` for every sign matrix
`S ∈ {−1, 1}^{k×k}`, the matrix `M` of Eq. (4) with `p = sin θ` is positive definite. -/
theorem eq_8 (k : ℕ) (hk : 1 ≤ k) (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    (∀ ℓ : EdgeLabel k,
      ((eigLambda ℓ (Real.tan θ) : ℝ) : ℂ) =
        (((Real.cos θ ^ (k ^ 2))⁻¹ : ℝ) : ℂ) * charFun (signMatOfLabel ℓ) θ) ∧
    ((∀ S : Matrix (Fin k) (Fin k) ℝ, IsSignMatrix S → 0 < charFun S θ) →
      (lowerBoundMatrix k (Real.sin θ)).PosDef) := by sorry

end DetConnSketch.Main
