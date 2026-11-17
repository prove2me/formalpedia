-- Prove2me | Theorems.Thm_BSCvsBEC_Supplement_theorem_3_3
-- name    : BSCvsBEC.Supplement.theorem_3_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T06:38:34.313341+00:00
-- url     : https://prove2.me/theorems/47f508a7-f95f-4ffd-8911-0e1fbd9a5410
-- title:
--   Theorem 3.3 — reverse $\tfrac12$-norm Samorodnitsky inequality $\|T_\rho f\|_{1/2}\ge\mathbb E_{S\sim\lambda}\|E_Sf\|_{1/2}$
-- statement:
--   Let $f:\mathbb F_2^n\to\mathbb R_{\ge0}$, let $0\le\rho\le1$ and let $\rho^2\le\lambda\le1$. Then
--   $$\|T_\rho f\|_{1/2}\ \ge\ \mathbb E_{S\sim\lambda}\|E_Sf\|_{1/2},$$
--   where $\|g\|_{1/2}=\big(\mathbb E_U\sqrt{|g(U)|}\big)^2$ for $U$ uniform on $\mathbb F_2^n$, $E_Sf(y)=\mathbb E[f(U)\mid U_S=y_S]$, $T_\rho f(y)=\sum_x\big(\tfrac{1-\rho}2\big)^{|x+y|}\big(\tfrac{1+\rho}2\big)^{n-|x+y|}f(x)$, and $S$ contains each coordinate independently with probability $\lambda$.
--
--   Applied to the density of a dual code, the right side is the MAP success probability on $\mathrm{BEC}_\lambda$ and the left side is the PSC guessing probability (Theorem 3.8); this gives Theorem 3.10.
--
--   Differences from the source:
--   - encoding: f : F₂ⁿ → ℝ≥0 → f : (Fin n → Fin 2) → ℝ with ∀ x, 0 ≤ f x; reason: Lean convention; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Theorem 3.3, eq. (65), p.14; ‖·‖_α, E_S, T_ρ: eqs. (18), (19), (21), p.6

import Mathlib
import Definitions.Def_BSCvsBEC_expectSubset
import Definitions.Def_BSCvsBEC_Supplement_lamStarB

namespace BSCvsBEC.Supplement

/-- **Theorem 3.3 (p.14).** Let `f : F₂ⁿ → ℝ≥0`, let `0 ≤ ρ ≤ 1`, and let `ρ² ≤ λ ≤ 1`. Then
`‖T_ρ f‖_{1/2} ≥ E_{S∼λ} ‖E_S f‖_{1/2}` (eq. (65)).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Theorem 3.3, eq. (65), p.14; `‖·‖_α`, `E_S`, `T_ρ` as in eqs. (18), (19), (21), p.6.

**Formalization Note.** `F₂ = Fin 2`; `f` is real-valued with `f ≥ 0`; `‖g‖_{1/2} = (2^{−n} ∑ₓ √|g(x)|)²`
(`unifNorm (1/2)`), `E_S` is `condExpS S` and `T_ρ` is `noiseN ρ` (`p = (1 − ρ)/2`). -/
theorem theorem_3_3 {n : ℕ} (f : (Fin n → Fin 2) → ℝ) (hf : ∀ x, 0 ≤ f x)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (lam : ℝ) (hl : ρ ^ 2 ≤ lam) (hl1 : lam ≤ 1) :
    BSCvsBEC.expectSubset lam n (fun S => unifNorm (1 / 2) (condExpS S f)) ≤
      unifNorm (1 / 2) (noiseN ρ f) := by sorry

end BSCvsBEC.Supplement
