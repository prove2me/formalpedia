-- Prove2me | Theorems.Thm_DetANN_expected_potential
-- name    : DetANN.expected_potential
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T12:26:29.210538+00:00
-- url     : https://prove2.me/theorems/61c2087d-371e-41b9-a19a-f87a2b243084
-- title:
--   §6.3, p.15 — under uniform signs $\mathbb E\Phi\le Nd\,(Cp_0/(L\tau^2))^{p_0}\le Nd\,4^{-p_0}\le1/8$
-- statement:
--   There are absolute constants $C>0$ (the constant of Lemma 6.1) and $C_0^*>0$ such that for every $C_0\ge C_0^*$ the following holds. Let $d\ge1$, let $h$ be a $d\times d$ matrix with entries in $\{-1,+1\}$, let $\tau\in(0,1)$, and let $\mathcal D\subseteq\mathbb R^d$ be a finite set of $N\ge1$ nonzero vectors. Put $p_0=\lceil\log_4(8Nd)\rceil$ and $L=\lceil C_0\tau^{-2}p_0\rceil$, and let $\Phi$ be the potential (24) of the signed blocks. If all $Ld$ signs are independent and uniform, then
--
--   $$\mathbb E\,\Phi\le Nd\left(\frac{Cp_0}{L\tau^2}\right)^{p_0}\le Nd\,4^{-p_0}\le\frac18 .$$
--
--   This is the estimate that the method of conditional expectations derandomizes in the proof of Theorem 3.2.
--
--   Differences from the source:
--   - generalization: 𝒟 one orientation of each nonzero difference of two database points → any finite set of N ≥ 1 nonzero vectors; reason: the set of oriented differences is such a set
--   - generalization: h the Walsh–Hadamard matrix (d a power of two) → any d × d matrix with entries ±1, any d ≥ 1; reason: the Walsh–Hadamard matrix has entries ±1
--   - reading: for a sufficiently large absolute constant C₀ (C the absolute constant of Lemma 6.1) → ∃ C > 0, ∃ C₀* > 0 such that the chain holds for every C₀ ≥ C₀*, uniformly in d, h, τ, 𝒟; reason: the standard meaning of 'sufficiently large absolute constant'; C₀* may depend on the absolute C, as the page's 'the second inequality follows from the choice of C₀' requires
--   - encoding: E over independent uniform signs → the uniform average over all ξ : Fin L → Fin d → Bool; reason: the same expectation
-- source:
--   Feng, Indyk, Deterministic Approximate Nearest Neighbors in High Dimensions, STOC 2027 submission (manuscript sha256 96f0ad57b9d12ba3ac6f9e61c88ddfd6b621e077d7e2a9821906e5b4ff0d0e82), §6.3, p.15 (PDF p.15)

import Mathlib
import Definitions.Def_DetANN_SignedBlocks

namespace DetANN

/-- **The expected potential** (Y. Feng, P. Indyk, *Deterministic Approximate Nearest Neighbors in High Dimensions*, STOC 2027
submission (manuscript sha256 96f0ad57…), §6.3, p.15).
Let `𝒟` be a finite set of `N ≥ 1` nonzero vectors of `ℝ^d`, `τ ∈ (0, 1)`, `p₀ = ⌈log₄(8Nd)⌉` and
`L = ⌈C₀ τ^{−2} p₀⌉` for a sufficiently large absolute constant `C₀`. Under independent uniform signs,
the potential (24) `Φ = ∑_{v ∈ 𝒟} ∑_j ((d‖A_j v‖² − r_v)/(τ r_v))^{2p₀}`, `r_v = ‖v‖²`, has
`EΦ ≤ Nd(Cp₀/(Lτ²))^{p₀} ≤ Nd·4^{−p₀} ≤ 1/8`, with `C` the absolute constant of Lemma 6.1.

**Formalization Note.** "Sufficiently large absolute constant `C₀`" is the threshold form: there is
`C₀* > 0` such that the bound holds for every `C₀ ≥ C₀*`, uniformly in `d`, `h`, `τ` and `𝒟`. The paper's
`𝒟` holds one orientation of each nonzero difference of two database points; here `𝒟` is any finite
set of nonzero vectors with `N = |𝒟| ≥ 1`. `h` is any `d × d` matrix with entries `±1` (the paper:
Walsh–Hadamard). `E` is the uniform average over all `ξ : Fin L → Fin d → Bool`. All three links of the printed chain
are stated. The absolute constant `C` (Lemma 6.1's) comes first, then the threshold `C₀*`, which may
depend on `C` ("the second inequality follows from the choice of `C₀`"). -/
theorem expected_potential :
    ∃ C : ℝ, 0 < C ∧ ∃ C₀s : ℝ, 0 < C₀s ∧ ∀ C₀ : ℝ, C₀s ≤ C₀ → ∀ d : ℕ, 1 ≤ d →
      ∀ h : Matrix (Fin d) (Fin d) ℝ, (∀ j r, h j r = 1 ∨ h j r = -1) →
        ∀ τ : ℝ, 0 < τ → τ < 1 →
          ∀ D : Finset (EuclideanSpace ℝ (Fin d)), (∀ v ∈ D, v ≠ 0) → 1 ≤ D.card →
            (Fintype.card (Fin (numReps C₀ τ (momentOrder D.card d)) → Fin d → Bool) : ℝ)⁻¹ *
                ∑ ξ : Fin (numReps C₀ τ (momentOrder D.card d)) → Fin d → Bool,
                  potential h (numReps C₀ τ (momentOrder D.card d)) ξ τ (momentOrder D.card d) D
              ≤ (D.card : ℝ) * d * (C * momentOrder D.card d /
                  ((numReps C₀ τ (momentOrder D.card d) : ℝ) * τ ^ 2)) ^ momentOrder D.card d ∧
            (D.card : ℝ) * d * (C * momentOrder D.card d /
                  ((numReps C₀ τ (momentOrder D.card d) : ℝ) * τ ^ 2)) ^ momentOrder D.card d
              ≤ (D.card : ℝ) * d * (4 : ℝ)⁻¹ ^ momentOrder D.card d ∧
            (D.card : ℝ) * d * (4 : ℝ)⁻¹ ^ momentOrder D.card d ≤ 1 / 8 := by sorry

end DetANN
