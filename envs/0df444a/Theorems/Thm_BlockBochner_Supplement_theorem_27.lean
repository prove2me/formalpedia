-- Prove2me | Theorems.Thm_BlockBochner_Supplement_theorem_27
-- name    : BlockBochner.Supplement.theorem_27
-- status  : Open
-- author  : @iris
-- created : 2026-11-16T08:34:41.098715+00:00
-- url     : https://prove2.me/theorems/e06b16ca-8bd6-4ab8-9e16-3a0b1b887828
-- title:
--   Theorem 27 — graphic matroids with arbitrary fugacities: $p_{ij}\le\frac43p_ip_j$
-- statement:
--   Let $G$ be a finite (multi)graph with edge set $E$, let $M=(E,\mathcal I)$ be its graphic matroid, whose independent sets are the forests of $G$, let $\lambda\in(0,\infty)^E$ be arbitrary positive fugacities, and let $\mu(F)\propto\prod_{i\in F}\lambda_i$ on forests $F$. With $p_i=\Pr_\mu[i\in F]$ and $p_{ij}=\Pr_\mu[i,j\in F]$, for all distinct edges $i,j\in E$,
--   $$
--   p_{ij}\ \le\ \frac43\,p_ip_j .
--   $$
--
--   For $\lambda\equiv1$ this is the bound $c=4/3$ in the negative-correlation inequality (2) for uniformly random forests (Theorem 7).
--
--   **Formalization Note** "$M$ is graphic" is the hypothesis that the independent finite sets of the Mathlib matroid $M$ are exactly the forests (`IsForestEdges`) of a finite multigraph with edge type $\alpha$ and endpoint map into `Sym2 W`.
--
--   Differences from the source:
--   - reading: M is graphic (independent sets are the forests of a graph; the paper does not say whether parallel edges or loops are allowed) → the independent sets of M are exactly the acyclic edge sets of a finite multigraph ends : α → Sym2 W (parallel edges and loops allowed); reason: the multigraph reading is the general one and contains simple graphs; graphic matroids are standardly cycle matroids of multigraphs
--   - encoding: finite matroid M = (E, I) → Mathlib Matroid on a finite type α with ground set Set.univ; reason: the same object
-- source:
--   Leake–Li, Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model, arXiv:2611.05228 (sha256 e4bc2683…4a27706), Theorem 27, p.31 (PDF p.32); setting Sec. 5, p.30 (PDF p.31)

import Mathlib
import Definitions.Def_BlockBochner_Supplement_inclProb
import Definitions.Def_BlockBochner_Supplement_IsForestEdges

namespace BlockBochner.Supplement

/-- **Theorem 27 (graphic matroids: `p_ij ≤ (4/3) p_i p_j`).** Leake–Li, *Beyond the Bochner Method: Optimal Spectral Gaps for Block Dynamics of Spin Systems like the O(N) Model*, arXiv:2611.05228, Theorem 27,
p.31: "If `M` is graphic, then for all distinct `i, j ∈ E`, `p_ij ≤ (4/3) p_i p_j`." The fugacities
are arbitrary positive numbers ("As above, the fugacities may be arbitrary positive numbers", p.31).

**Formalization Note** "`M` is graphic": the independent sets of `M` are exactly the forests of a
finite multigraph with edge set `α` and endpoint map `ends : α → Sym2 W` (parallel edges and loops
allowed; simple graphs are a special case). -/
theorem theorem_27 {α W : Type*} [Fintype α] [DecidableEq α] [Finite W] (M : Matroid α)
    (hE : M.E = Set.univ) (ends : α → Sym2 W)
    (hM : ∀ S : Finset α, M.Indep ↑S ↔ IsForestEdges ends S) (lam : α → ℝ)
    (hlam : ∀ i, 0 < lam i) :
    ∀ i j, i ≠ j → inclProb (fun S => M.Indep ↑S) lam {i, j} ≤
      4 / 3 * inclProb (fun S => M.Indep ↑S) lam {i} * inclProb (fun S => M.Indep ↑S) lam {j} := by sorry

end BlockBochner.Supplement
