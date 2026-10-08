-- Prove2me | Theorems.Thm_ExtADMM_Diverge_spectral_radius
-- name    : ExtADMM.Diverge.spectral_radius
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T22:06:05.160379+00:00
-- url     : https://prove2.me/theorems/4032b3b3-ac9d-42e5-a5df-ced8d8030bc2
-- title:
--   p. 13 — ρ(M) = |d₁| = |d₂| > 1 for the iteration matrix M of (3.10)
-- statement:
--   Let $M$ be the $5\times5$ real matrix of p. 12,
--
--   $$M=\frac{1}{162}\begin{pmatrix}144&-9&-9&-9&18\\8&157&-5&13&-8\\64&122&122&-58&-64\\56&-35&-35&91&-56\\-88&-26&-26&-62&88\end{pmatrix}.$$
--
--   Then $M$ has a non-real complex eigenvalue $d_1$ whose modulus is the spectral radius of $M$ and exceeds one: writing $d_2=\overline{d_1}$ (also an eigenvalue, since $M$ is real),
--
--   $$\rho(M)=|d_1|=|d_2|>1 .$$
--
--   The spectral radius exceeding one is the source of the divergence of the extended ADMM on example (3.10). Numerically $|d_1|\approx1.0278$; this value is not part of the statement.
--
--   **Formalization Note.** Eigenvalues are the complex roots of the characteristic polynomial of $M$ regarded as a complex matrix. "$\rho(M)=|d_1|$" is stated as: every complex root $e$ satisfies $|e|\le|d_1|$. "$d_1\ne d_2=\overline{d_1}$" is stated as $\operatorname{Im} d_1\neq0$. The eigenvalues printed in (3.11) are four-digit roundings and are not used.
-- source:
--   Chen, He, Ye & Yuan, The direct extension of ADMM for multi-block convex minimization problems is not necessarily convergent, Math. Program., DOI 10.1007/s10107-014-0826-5 (authors' version of January 22, 2014), p. 13, after (3.11)

import Mathlib
import Definitions.Def_ExtADMM_Diverge_Setting

open Matrix Filter Topology

namespace ExtADMM.Diverge

/-- p. 13: `ρ(M) = |d₁| = |d₂| > 1`. The matrix `M310`, viewed over `ℂ`, has a non-real
eigenvalue `d` (so `d` and `d̄` are two distinct eigenvalues of the same modulus) with
`|d| > 1`, and every eigenvalue `e` of `M310` satisfies `|e| ≤ |d|`. -/
theorem spectral_radius :
    ∃ d : ℂ, d.im ≠ 0 ∧ ((M310.map (algebraMap ℝ ℂ)).charpoly).IsRoot d ∧ 1 < ‖d‖ ∧
      ∀ e : ℂ, ((M310.map (algebraMap ℝ ℂ)).charpoly).IsRoot e → ‖e‖ ≤ ‖d‖ := by sorry

end ExtADMM.Diverge
