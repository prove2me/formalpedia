-- Prove2me | Theorems.Thm_CompOT_EntropicDual_proposition_4_5
-- name    : CompOT.EntropicDual.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T02:33:33.800995+00:00
-- url     : https://prove2.me/theorems/165f8cc1-076e-401c-b73f-cb9eae47dd42
-- title:
--   Proposition 4.5 — entropic dual maximizers are Kantorovich feasible
-- statement:
--   Let $a\in\Sigma_n$ and $b\in\Sigma_m$ be probability histograms, let $C\in\mathbb R^{n\times m}$, and let $\varepsilon>0$. Every pair $(f,g)$ maximizing the entropic dual objective $Q$ satisfies $f_i+g_j\le C_{ij}$ for every $i,j$. Consequently,
--
--   $$
--   \langle f,a\rangle+\langle g,b\rangle\le L_C(a,b),
--   $$
--
--   where $L_C$ is the unregularized Kantorovich cost. Thus the entropic dual potentials supply a feasible lower bound for ordinary optimal transport.
--
--   **Formalization Note** A maximizer is a pair whose objective dominates all pairs; the real infimum defining $L_C$ is only used with nonempty, bounded coupling sets. If a histogram has a zero entry, there is no finite maximizer, so the conditional statement has no instance there.
-- source:
--   Peyré & Cuturi, Computational Optimal Transport (FnT ML 2019), Proposition 4.5, pp. 452–453. https://doi.org/10.1561/2200000073

import Mathlib
import Definitions.Def_CompOT_EntropicDual_Defs

namespace CompOT.EntropicDual

/-- Proposition 4.5, pp. 452–453: every entropic dual maximizer is a feasible
Kantorovich potential and its linear objective is below the unregularized cost. -/
theorem proposition_4_5 {n m : ℕ} (C : Matrix (Fin n) (Fin m) ℝ)
    (a : Fin n → ℝ) (b : Fin m → ℝ) (ε : ℝ)
    (hn : 0 < n) (hm : 0 < m) (hε : 0 < ε)
    (ha : a ∈ stdSimplex ℝ (Fin n)) (hb : b ∈ stdSimplex ℝ (Fin m))
    (f : Fin n → ℝ) (g : Fin m → ℝ)
    (hmax : ∀ f' g', dualObjEnt C a b ε f' g' ≤ dualObjEnt C a b ε f g) :
    KantorovichFeasible C f g ∧
      (∑ i, f i * a i) + (∑ j, g j * b j) ≤ unregCost C a b := by sorry

end CompOT.EntropicDual
