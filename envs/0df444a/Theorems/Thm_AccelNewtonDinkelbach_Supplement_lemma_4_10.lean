-- Prove2me | Theorems.Thm_AccelNewtonDinkelbach_Supplement_lemma_4_10
-- name    : AccelNewtonDinkelbach.Supplement.lemma_4_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T01:06:08.861151+00:00
-- url     : https://prove2.me/theorems/ad4b8724-5bd2-5a90-890a-7f98572d59d4
-- title:
--   Lemma 4.10 — optimal paths at decreasing parameters satisfy subpath monotonicity
-- statement:
--   Let $\delta^{(1)}>\cdots>\delta^{(\ell)}$ be strictly decreasing reals. If $P^{(i)}$ is a simple $u$-$u'$ path whose unit generalized flow is primal optimal for $f(\delta^{(i)})$, then for $i<j$ and every shared $v\ne u$,
--
--   $$\gamma(P^{(i)}_{uv})\le\gamma(P^{(j)}_{uv}).$$
--
--   Differences from the source:
--   - reading: a decreasing sequence of iterates → any strictly decreasing real sequence; reason: the lemma and its proof use only the order and primal optimality, so this is the literal mathematical content of the displayed hypotheses
--   - generalization: paths in the full split graph G_u → paths in any active split subgraph A; reason: the full graph is the instance A = E and Algorithm 3 uses phase subgraphs
-- source:
--   Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 4.10, p.17

import Mathlib
import Definitions.Def_AccelNewtonDinkelbach_Supplement_M2VPIFractional
import Definitions.Def_AccelNewtonDinkelbach_Supplement_SubpathMonotone

namespace AccelNewtonDinkelbach.Supplement

set_option autoImplicit false

/-- **Lemma 4.10 (subpath monotonicity of optimal paths).**
Dadush, Koh, Natura, Végh, arXiv:2004.08634v4, Lemma 4.10, p.17. -/
theorem lemma_4_10 {n m ℓ : ℕ} (M : M2VPI n m) (A : Fin m → Prop) (u : Fin n)
    (δ : Fin ℓ → ℝ) (P : Fin ℓ → M.SplitWalk A u)
    (hdec : ∀ i j : Fin ℓ, i < j → δ j < δ i)
    (hpath : ∀ i, (P i).start = some u ∧ (P i).finish = none ∧ (P i).IsPath)
    (hopt : ∀ i, M.PrimalOptimal A u (δ i) (M.pathUnitFlow (P i).edges)) :
    M2VPI.SubpathMonotone P := by sorry

end AccelNewtonDinkelbach.Supplement
