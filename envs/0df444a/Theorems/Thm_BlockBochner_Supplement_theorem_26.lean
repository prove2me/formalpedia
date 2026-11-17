-- Prove2me | Theorems.Thm_BlockBochner_Supplement_theorem_26
-- name    : BlockBochner.Supplement.theorem_26
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:34:09.695302+00:00
-- url     : https://prove2.me/theorems/2d75632c-e202-4ad1-953e-42b17314321f
-- title:
--   Theorem 26 — matroids with arbitrary fugacities: $\Sigma\preceq\mathrm{diag}(p)$, hence $p_{ij}\le2p_ip_j$
-- statement:
--   Let $M=(E,\mathcal I)$ be a finite matroid, $\lambda\in(0,\infty)^E$ an arbitrary positive fugacity vector, and $\mu(S)\propto\prod_{i\in S}\lambda_i$ the fugacity measure on independent sets. For $X\sim\mu$ let $p_i=\Pr_\mu[i\in X]$, $p_{ij}=\Pr_\mu[i,j\in X]$ and $\Sigma=(\mathrm{Cov}_\mu(\mathbf 1\{i\in X\},\mathbf 1\{j\in X\}))_{i,j\in E}$. Then
--
--   1. in the Loewner order,
--   $$
--   \Sigma\ \preceq\ \mathrm{diag}(p);
--   $$
--   2. consequently, for all distinct $i,j\in E$,
--   $$
--   p_{ij}\ \le\ 2\,p_ip_j .
--   $$
--
--   This recovers the constant $c=2$ in the negative-correlation inequality (2) for matroid independent sets, for every positive weighting.
--
--   **Formalization Note** $M$ is a Mathlib matroid on a finite type with ground set the whole type; $\Sigma\preceq\mathrm{diag}(p)$ is "$\mathrm{diag}(p)-\Sigma$ is positive semidefinite".
--
--   Differences from the source:
--   - encoding: finite matroid M = (E, I) → Mathlib Matroid on a finite type α with ground set Set.univ, independent finite sets M.Indep; reason: the same object; a matroid on a subset of a type restricts to one on its ground type
--   - encoding: Σ ⪯ diag(p) → (diag(p) − Σ).PosSemidef; reason: the definition of the Loewner order
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Theorem 26, p.31 (PDF p.32); setting Sec. 5, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_inclProb
import Definitions.Def_BlockBochner_Supplement_covMat

namespace BlockBochner.Supplement

/-- **Theorem 26 (matroids: `Σ ⪯ diag(p)`).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 26, p.31 (setting
Sec. 5, p.30): "We have `Σ ⪯ diag(p)`. Consequently, for all distinct `i, j ∈ E`, `p_ij ≤ 2 p_i p_j`."
Here `M = (E, I)` is a finite matroid, `λ ∈ (0,∞)^E` an arbitrary fugacity vector,
`µ(S) ∝ Π_{i∈S} λ_i` on `I`, `p_i = Pr[i ∈ X]`, `p_ij = Pr[i, j ∈ X]`, `Σ = (Cov_µ(X_i, X_j))`.

**Formalization Note** `M` is a Mathlib matroid on the finite type `α` with ground set all of `α`.
`Σ ⪯ diag(p)` is the Loewner order: `diag(p) − Σ` is positive semidefinite. -/
theorem theorem_26 {α : Type*} [Fintype α] [DecidableEq α] (M : Matroid α)
    (hE : M.E = Set.univ) (lam : α → ℝ) (hlam : ∀ i, 0 < lam i) :
    (Matrix.diagonal (fun i => inclProb (fun S => M.Indep ↑S) lam {i}) -
        covMat (fun S => M.Indep ↑S) lam).PosSemidef ∧
      ∀ i j, i ≠ j → inclProb (fun S => M.Indep ↑S) lam {i, j} ≤
        2 * inclProb (fun S => M.Indep ↑S) lam {i} * inclProb (fun S => M.Indep ↑S) lam {j} := by sorry

end BlockBochner.Supplement
