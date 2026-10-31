-- Prove2me | Theorems.Thm_CombOpt_TotalUnimodularity_inv_mulVec_integral_iff_det
-- name    : CombOpt.TotalUnimodularity.inv_mulVec_integral_iff_det
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:04:18.472173+00:00
-- url     : https://prove2.me/theorems/2b0302f5-5cda-4995-9f11-3d69e1c43677
-- title:
--   Proposition 6.23 — $A^{-1}b$ is integral for all integral $b$ iff $\det A=\pm1$
-- statement:
--   Let $A$ be an integral, nonsingular $m\times m$ matrix. Then
--   $$A^{-1}b\in\mathbb Z^m\ \text{ for every } b\in\mathbb Z^m \quad\Longleftrightarrow\quad \det A = 1 \ \text{ or }\ \det A=-1.$$
--
--   This is the square case of unimodularity: a basis with determinant $\pm1$ is exactly one whose basic solutions are integral for all integral right-hand sides. It is the key step in both directions of the Veinott–Dantzig theorem.
--
--   **Formalization Note** $A$ has integer entries; nonsingularity and $A^{-1}$ refer to its real cast. An integral $b\in\mathbb R^m$ is the cast of $b\in\mathbb Z^m$, and "$A^{-1}b$ is integral" means it is the cast of some $z\in\mathbb Z^m$.
--
--   Differences from the source:
--   - encoding: integral matrix $A$, integral vectors $b, A^{-1}b\in\mathbb R^m$ → `Matrix (Fin m) (Fin m) ℤ`, its real cast, and real casts of `Fin m → ℤ`; reason: Lean convention for integral data; same instances
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Proposition 6.23, p. 220 (PDF p. 228)

import Mathlib

namespace CombOpt.TotalUnimodularity

open Matrix

/-- **Proposition 6.23 (square unimodular matrices).**
Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998),
Proposition 6.23, p. 220 (PDF p. 228): "Let A be an integral, nonsingular, m by m matrix. Then
A⁻¹b is integral for every integral vector b ∈ Rᵐ if and only if det(A) = 1 or −1."

For an integer `m × m` matrix `A` that is nonsingular (its real cast has nonzero determinant),
the real vector `A⁻¹ b` has integer coordinates for every `b ∈ ℤᵐ` if and only if
`det A = 1` or `det A = −1`.

**Formalization Note.** `A` has entries in `ℤ`; the inverse is taken of its real cast
`A.map (Int.cast)`, and an integral vector `b ∈ ℝᵐ` is the real cast of some `b : Fin m → ℤ`.
"`A⁻¹ b` is integral" means it is the real cast of some `z : Fin m → ℤ`. -/
theorem inv_mulVec_integral_iff_det {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).det ≠ 0) :
    (∀ b : Fin m → ℤ, ∃ z : Fin m → ℤ,
        (A.map (Int.cast : ℤ → ℝ))⁻¹ *ᵥ (fun i => (b i : ℝ)) = fun i => (z i : ℝ)) ↔
      (A.det = 1 ∨ A.det = -1) := by sorry

end CombOpt.TotalUnimodularity
