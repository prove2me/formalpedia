-- Prove2me | Theorems.Thm_BSCvsBEC_section4_bec_identity
-- name    : BSCvsBEC.section4_bec_identity
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T08:40:42.757386+00:00
-- url     : https://prove2.me/theorems/981620a0-f681-4a27-8a62-ea094be7614e
-- title:
--   §4 identity: $H(X\mid \mathrm{BEC}_\lambda(X))=H(X)-\mathbb E_{R\sim1-\lambda}H(X_R)$
-- statement:
--   Let $0\le\lambda\le1$ and let $X\in\mathbb F_2^n$ be a random variable with pmf $P$. Through $\mathrm{BEC}_\lambda$ each coordinate is revealed independently with probability $1-\lambda$; writing $R\subseteq[n]$ for the set of revealed coordinates,
--   $$H(X\mid \mathrm{BEC}_\lambda(X))=H(X)-\mathbb E_{R\sim1-\lambda}\,H(X_R).$$
--   The left side is $H(XY)-H(Y)$ of the joint distribution of $X$ and $Y=\mathrm{BEC}_\lambda(X)$.
--
--   At $\lambda=\cos^2\theta$ this is the paper's identity $H(X\mid\mathrm{BEC}_{\cos^2\theta}(X))=H(X)-\mathbb E_{R\sim\sin^2\theta}[H(X_R)]$, which reduces Theorem 1.3 to Theorem 4.1.
--
--   Differences from the source:
--   - generalization: λ = cos²θ, R ∼ sin²θ → every λ ∈ [0, 1], R ∼ 1 − λ; reason: the same computation; λ = cos²θ gives 1 − λ = sin²θ, the page's case, and the goal needs it for every λ ≥ cos²θ
--   - encoding: a random variable X on a finite set → its pmf P with IsPMF P; reason: Lean convention; same instances
-- source:
--   J. Hązła, R. O'Donnell, BSC vs. BEC vs. PSC, manuscript of November 3, 2026 (STOC 2027 submission, preprint basis, sha256 a44ed9262ff4e01c0cbd7e204728d4ad8bf4cfda8dbf126b96022d4c84b56186), §4, p.18

import Mathlib
import Definitions.Def_BSCvsBEC_shannon
import Definitions.Def_BSCvsBEC_expectSubset
import Definitions.Def_BSCvsBEC_condEntBEC

namespace BSCvsBEC

/-- **§4, p.18 (BEC identity).** For a random `X ∈ F₂ⁿ` with pmf `P` and `0 ≤ λ ≤ 1`,
`H(X | BEC_λ(X)) = H(X) − E_{R∼1−λ} H(X_R)`, where `R` is the set of revealed coordinates (each
revealed independently with probability `1 − λ`).
Hązła–O'Donnell, *BSC vs. BEC vs. PSC*, manuscript of November 3, 2026 (STOC 2027 submission,
sha256 a44ed926…), §4, p.18: "regarding `H(X | BEC_{cos²θ}(X))`, this is equal to `H(X) − E_{R∼sin²θ}[H(X_R)]`, if
`R ⊆ [n]` denotes the set of randomly revealed coordinates."

**Formalization Note.** Stated for every `λ ∈ [0, 1]`; the page's case is `λ = cos²θ`,
`1 − λ = sin²θ`. -/
theorem section4_bec_identity (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) {n : ℕ}
    (P : (Fin n → Fin 2) → ℝ) (hP : IsPMF P) :
    condEntBEC lam P = shannon P - expectSubset (1 - lam) n (fun R => shannon (margR R P)) := by sorry

end BSCvsBEC
