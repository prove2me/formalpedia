-- Prove2me | Theorems.Thm_BSCvsBEC_claim_2_13
-- name    : BSCvsBEC.claim_2_13
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:33:29.900187+00:00
-- url     : https://prove2.me/theorems/ae2e4164-5e2b-4378-973a-76e18d7c7b20
-- title:
--   Claim 2.13: $c_-I\preceq xA+yB\preceq c_+I$ implies $xa+yb\in[c_-,c_+]$ $\mu$-a.e.
-- statement:
--   Let $A,B$ be Hermitian matrices and $\mu$ a measure on $\mathbb R^2$ with the property (58) of Theorem 2.12 (a tracial joint spectral measure of $(A,B)$). Let $x,y\in\mathbb R$. If
--   $$c_-I\ \preceq\ xA+yB\ \preceq\ c_+I$$
--   in the positive semidefinite order for some $c_-\le0$ and $c_+\ge0$, then $xa+yb\in[c_-,c_+]$ for $\mu$-almost every $(a,b)$.
--
--   For positive semidefinite $A,B$ this gives $(a,b)\in[0,\|A\|]\times[0,\|B\|]$ $\mu$-a.e., and $b\le qa$ $\mu$-a.e. when $B\preceq qA$.
--
--   Differences from the source:
--   - generalization: μ = μ_{A,B}, the measure of Theorem 2.12 → every measure μ with property (58) (IsTJSM A B μ); reason: the proof uses only (58); the measure of Theorem 2.12 is one such μ
--   - encoding: c₋I ≤ xA + yB ≤ c₊I (PSD order) → xA + yB − c₋I and c₊I − (xA + yB) positive semidefinite; reason: definition of the PSD order
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), Claim 2.13, p.12

import Mathlib
import Definitions.Def_BSCvsBEC_IsTJSM

open MeasureTheory
open scoped ComplexOrder

namespace BSCvsBEC

/-- **Claim 2.13 (p.12).** Let `μ` be a tracial joint spectral measure of the Hermitian pair `(A, B)`
(Theorem 2.12). If `c₋ I ⪯ xA + yB ⪯ c₊ I` (PSD order) for some `c₋ ≤ 0` and `c₊ ≥ 0`, then
`xa + yb ∈ [c₋, c₊]` for `μ`-almost every `(a, b)`.
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), Claim 2.13, p.12.

**Formalization Note.** Stated for every measure `μ` with property (58) (`IsTJSM A B μ`), not only
for a particular choice of `μ_{A,B}`. -/
theorem claim_2_13 (ι : Type) [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℂ)
    (hA : A.IsHermitian) (hB : B.IsHermitian) (μ : Measure (ℝ × ℝ)) (hμ : IsTJSM A B μ)
    (x y cm cp : ℝ) (hcm : cm ≤ 0) (hcp : 0 ≤ cp)
    (hlo : (x • A + y • B - ((cm : ℝ) : ℂ) • (1 : Matrix ι ι ℂ)).PosSemidef)
    (hhi : (((cp : ℝ) : ℂ) • (1 : Matrix ι ι ℂ) - (x • A + y • B)).PosSemidef) :
    ∀ᵐ p ∂μ, x * p.1 + y * p.2 ∈ Set.Icc cm cp := by sorry

end BSCvsBEC
