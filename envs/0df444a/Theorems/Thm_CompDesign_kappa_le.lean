-- Prove2me | Theorems.Thm_CompDesign_kappa_le
-- name    : CompDesign.kappa_le
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T05:54:57.172605+00:00
-- url     : https://prove2.me/theorems/a43bec42-55e7-4831-bcb6-ba875f0eedcf
-- title:
--   §5.1 — $\kappa(\lambda)\le 1/(1-\lambda)$
-- statement:
--   Let $\kappa(\lambda)=\max\{\sum_{i\in S}\frac{x_i}{1-x_i}:0\le x_i\le\lambda,\ \sum_i x_i\le 1,\ S \text{ finite}\}$ be the cost concentration term (20). For $0\le\lambda<1$,
--   $$\kappa(\lambda)\le\frac{1}{1-\lambda}.$$
--
--   This is the "immediate upper bound" stated after (20); it is what turns the constant $1+\kappa(\lambda)$ of Theorem 5.1 into $(2-\lambda)/(1-\lambda)$.
--
--   **Formalization Note** `λ` is written `l`.
--
--   Differences from the source:
--   - reading: κ(λ) ≤ 1/(1−λ), with λ = max_i c_i/B ≪ 1 (no range printed) → hypotheses 0 ≤ l and l < 1; reason: the right-hand side is undefined at λ = 1 and negative beyond, and κ(λ) is infinite for λ ≥ 1; λ ≥ 0 because costs are nonnegative, and Main Result 2 assumes λ < 1
-- source:
--   Anagnostides, Bhawalkar, Liaw, Mehta, Paes Leme, Teng, Velegkas, Zheng, Compensation Design, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…), §5.1, after eq. (20), p.26 (PDF 29)

import Mathlib
import Definitions.Def_CompDesign_kappa

namespace CompDesign

/-- The upper bound `κ(λ) ≤ 1/(1 − λ)` stated after (20), §5.1, p.26 (PDF 29) of Anagnostides et al., *Compensation Design*, arXiv:2607.14438 (version of November 3, 2026, sha256 3d305d4d…).

**Formalization Note.** `λ` is a Lean keyword and is written `l`. The hypothesis `0 ≤ l < 1` is the
range where (20) is finite (Main Result 2 assumes `λ < 1`). -/
theorem kappa_le (l : ℝ) (hl0 : 0 ≤ l) (hl1 : l < 1) : kappa l ≤ 1 / (1 - l) := by sorry

end CompDesign
