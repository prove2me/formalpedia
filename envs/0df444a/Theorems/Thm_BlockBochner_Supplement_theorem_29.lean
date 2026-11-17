-- Prove2me | Theorems.Thm_BlockBochner_Supplement_theorem_29
-- name    : BlockBochner.Supplement.theorem_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:35:14.436781+00:00
-- url     : https://prove2.me/theorems/65792a91-4ee3-42ec-958a-89497da2877f
-- title:
--   Theorem 29 — forests: $\Sigma\preceq\frac34\mathrm{diag}(p)+\frac14S$ and $4(p_{ij}-p_ip_j)\le s_{ij}\le p_{ij}$
-- statement:
--   Let $G$ be a finite (multi)graph with edge set $E$ and $M$ its graphic matroid, let $\lambda\in(0,\infty)^E$ be arbitrary positive fugacities and $\mu(F)\propto\prod_{i\in F}\lambda_i$ on forests $F$. Let $p_i$, $p_{ij}$, $\Sigma$ be as in Theorem 26, and let
--   $$
--   s_{ij}=\Pr_\mu[i,j\text{ are edges of the same tree component of }F],\qquad S=(s_{ij})_{i,j\in E}.
--   $$
--   Then
--
--   1. in the Loewner order,
--   $$
--   \Sigma\ \preceq\ \tfrac34\,\mathrm{diag}(p)+\tfrac14\,S; \tag{23}
--   $$
--   2. for all distinct $i,j\in E$,
--   $$
--   4\,(p_{ij}-p_ip_j)\ \le\ s_{ij}\ \le\ p_{ij};
--   $$
--   3. consequently, for all distinct $i,j\in E$, $p_{ij}\le\frac43\,p_ip_j$.
--
--   **Formalization Note** As in Theorem 27, graphicness is the hypothesis that the independent finite sets of $M$ are the forests of a finite multigraph. $\preceq$ is the Loewner order: the difference is positive semidefinite. All three clauses are stated.
--
--   Differences from the source:
--   - reading: M is graphic (independent sets are the forests of a graph; the paper does not say whether parallel edges or loops are allowed) → the independent sets of M are exactly the acyclic edge sets of a finite multigraph ends : α → Sym2 W (parallel edges and loops allowed); reason: the multigraph reading is the general one and contains simple graphs; graphic matroids are standardly cycle matroids of multigraphs
--   - encoding: finite matroid M = (E, I) → Mathlib Matroid on a finite type α with ground set Set.univ; reason: the same object
--   - encoding: Σ ⪯ (3/4)diag(p) + (1/4)S → ((3/4)diag(p) + (1/4)S − Σ).PosSemidef; reason: the definition of the Loewner order
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Theorem 29, p.33 (PDF p.34); setting Sec. 5, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_inclProb
import Definitions.Def_BlockBochner_Supplement_covMat
import Definitions.Def_BlockBochner_Supplement_IsForestEdges
import Definitions.Def_BlockBochner_Supplement_sameTreeProb

namespace BlockBochner.Supplement

/-- **Theorem 29 (forests).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 29, p.33 (Sec. 5.3): "We have
`Σ ⪯ (3/4) diag(p) + (1/4) S` (23). Moreover, for all distinct `i, j ∈ E`,
`4(p_ij − p_i p_j) ≤ s_ij ≤ p_ij`. Consequently, `p_ij ≤ (4/3) p_i p_j`." Here `µ` is the fugacity
measure (arbitrary positive `λ`) on the forests of a graph and `s_ij` is the probability that
`i, j` are edges of the same tree component of `F ∼ µ`.

**Formalization Note** As in Theorem 27, the matroid `M` has the forests of the multigraph
`ends : α → Sym2 W` as its independent sets. `⪯` is the Loewner order (the difference is positive
semidefinite). All three clauses are stated. -/
theorem theorem_29 {α W : Type*} [Fintype α] [DecidableEq α] [Finite W] (M : Matroid α)
    (hE : M.E = Set.univ) (ends : α → Sym2 W)
    (hM : ∀ S : Finset α, M.Indep ↑S ↔ IsForestEdges ends S) (lam : α → ℝ)
    (hlam : ∀ i, 0 < lam i) :
    ((3 / 4 : ℝ) • Matrix.diagonal (fun i => inclProb (fun S => M.Indep ↑S) lam {i}) +
        (1 / 4 : ℝ) • Matrix.of (fun i j => sameTreeProb ends (fun S => M.Indep ↑S) lam i j) -
        covMat (fun S => M.Indep ↑S) lam).PosSemidef ∧
      (∀ i j, i ≠ j →
        4 * (inclProb (fun S => M.Indep ↑S) lam {i, j} -
            inclProb (fun S => M.Indep ↑S) lam {i} * inclProb (fun S => M.Indep ↑S) lam {j}) ≤
          sameTreeProb ends (fun S => M.Indep ↑S) lam i j ∧
        sameTreeProb ends (fun S => M.Indep ↑S) lam i j ≤ inclProb (fun S => M.Indep ↑S) lam {i, j}) ∧
      ∀ i j, i ≠ j → inclProb (fun S => M.Indep ↑S) lam {i, j} ≤
        4 / 3 * inclProb (fun S => M.Indep ↑S) lam {i} * inclProb (fun S => M.Indep ↑S) lam {j} := by sorry

end BlockBochner.Supplement
