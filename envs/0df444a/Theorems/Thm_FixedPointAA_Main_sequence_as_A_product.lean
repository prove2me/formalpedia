-- Prove2me | Theorems.Thm_FixedPointAA_Main_sequence_as_A_product
-- name    : FixedPointAA.Main.sequence_as_A_product
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T23:02:06.580921+00:00
-- url     : https://prove2.me/theorems/bf54fb97-c8b0-4cd3-86e5-3ee26f35348a
-- title:
--   Eqs. (12)–(13), p. 3 — sequence in output Z-rotation form
-- statement:
--   For $0<\lambda\le1$, $0<\delta\le1$, and $L=2l+1$, use the phases of Eq. (11). The output of the Grover sequence agrees, up to a unit global scalar $\omega$ and an output $Z$ rotation $R_0(\theta)$, with the ordered product of equatorial rotations:
--
--   $$\mathcal S_L|s\rangle=\omega R_0(\theta)A_{\zeta_L}\cdots A_{\zeta_1}|\bar t\rangle.$$
--
--   The phases $\zeta_k$ satisfy Eq. (13) and are palindromic modulo $2\pi$: $e^{i\zeta_k}=e^{i\zeta_{L-k+1}}$ for $1\le k\le L$. This isolates the amplitude-preserving correction to printed Eq. (12).
--
--   **Formalization Note** The paper's printed outer rotations in Eq. (12) do not yield the displayed vector even up to a global phase. The free output $Z$ rotation is the numerically verified corrected form; it preserves both coordinate magnitudes.
-- source:
--   Yoder, Low, Chuang, Fixed-point quantum search with an optimal number of queries, arXiv:1409.3305v2, p. 3, Eqs. (12)–(13)

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting

namespace FixedPointAA.Main
open scoped Matrix

/-- Eq. (12) up to global phase and an output Z rotation, with Eq. (13)'s palindrome. -/
theorem sequence_as_A_product (lam δ : ℝ) (hlam0 : 0 < lam) (hlam1 : lam ≤ 1)
    (hδ0 : 0 < δ) (hδ1 : δ ≤ 1) (l : ℕ) :
    (∃ ω : ℂ, ‖ω‖ = 1 ∧ ∃ θ : ℝ,
      seqOp (sVec lam) tVec (alpha l δ) (beta l δ) l *ᵥ sVec lam =
        ω • ((R 0 θ * Aprod (blochAngle lam) (zeta l δ) (2 * l + 1)) *ᵥ tbarVec)) ∧
    (∀ k : ℕ, 1 ≤ k → k ≤ 2 * l + 1 →
      Complex.exp ((zeta l δ k : ℂ) * Complex.I) =
        Complex.exp ((zeta l δ (2 * l + 2 - k) : ℂ) * Complex.I)) := by sorry

end FixedPointAA.Main
