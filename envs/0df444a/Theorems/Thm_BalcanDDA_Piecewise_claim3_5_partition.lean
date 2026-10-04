-- Prove2me | Theorems.Thm_BalcanDDA_Piecewise_claim3_5_partition
-- name    : BalcanDDA.Piecewise.claim3_5_partition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:16:43.849736+00:00
-- url     : https://prove2.me/theorems/26e625c4-9984-4526-94da-169b964d47f1
-- title:
--   Claim 3.5 — partition into at most $(ekN)^{\mathrm{VCdim}(\mathcal G^*)}$ cells on which the duals are piece functions
-- statement:
--   Let $\mathcal X$ be a set of problem instances and $\mathcal U \subseteq \mathbb R^{\mathcal X}$ a class of utility functions. Suppose the dual class $\mathcal U^*$ is $(\mathcal F, \mathcal G, k)$-piecewise decomposable with boundary functions $\mathcal G \subseteq \{0,1\}^{\mathcal U}$ and piece functions $\mathcal F \subseteq \mathbb R^{\mathcal U}$, where $k \ge 1$, and that $\mathrm{VCdim}(\mathcal G^*) = d_G$. Fix $N \ge 1$ and instances $x_1, \dots, x_N \in \mathcal X$.
--
--   Then there are $M$ nonempty sets $\mathcal U_1, \dots, \mathcal U_M$ partitioning $\mathcal U$, with
--   $$M \le (ekN)^{d_G}, \qquad\text{and } M < (ekN)^{d_G} \text{ when } d_G \ge 1,$$
--   such that for each cell $\mathcal U_j$ there exist piece functions $f_1, \dots, f_N \in \mathcal F$ with
--   $$u(x_i) = u^*_{x_i}(u) = f_i(u) \qquad \text{for all } u \in \mathcal U_j \text{ and } i \in \{1, \dots, N\}.$$
--
--   Within one cell, all $N$ dual functions are simultaneously given by fixed piece functions; this reduces the counting of labelings of $x_1, \dots, x_N$ to counting labelings by piece functions on each cell.
--
--   **Formalization Note.** The paper partitions the parameter space $\mathcal P$; since every object involved is a function of $u_\rho$ only, the cells are taken as subsets of $\mathcal U$ itself. The partition is the family of fibres of a surjection $\mathrm{cell} : \mathcal U \to \{0, \dots, M-1\}$. The printed bound is strict ($M < (ekN)^{\mathrm{VCdim}(\mathcal G^*)}$). It is kept strict whenever $d_G \ge 1$; when $d_G = 0$ the strict form is false (then $M = 1 = (ekN)^0$ for $\mathcal U \ne \emptyset$), so in that case only $M \le (ekN)^0$ is claimed (correction). $k \ge 1$ and $N \ge 1$ are added so that $kN \ge 1$ in that lemma.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 9, Claim 3.5 (setup: proof of Theorem 3.3, p. 8)

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_GrowthFunction
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim
import Definitions.Def_BalcanDDA_Piecewise_dual
import Definitions.Def_BalcanDDA_Piecewise_PiecewiseDecomposable

open FoundationsML.RademacherVC

namespace BalcanDDA.Piecewise

/-- Claim 3.5 (Balcan et al., arXiv:1908.02894v4, p. 9), with the parameter space indexed by
the class `U` itself. If `U*` is `(F, G, k)`-piecewise decomposable, `VCdim(G*) = dG`,
`k ≥ 1` and `N ≥ 1`, then for any instances `x₁, …, x_N` there is a partition of `U` into
`M ≤ (ekN)^{dG}` nonempty cells (the fibres of the surjection `cell`) such that on each cell
there are piece functions `f₁, …, f_N ∈ F` with `u(x_i) = f_i(u)` for every `u` in the cell
and every `i`. Correction: the printed strict `M < (ekN)^{dG}` is kept for `dG ≥ 1`; for
`dG = 0` it is false (`M = 1 = (ekN)^0` when `U ≠ ∅`), so only `M ≤ (ekN)^{dG}` is claimed there. -/
theorem claim3_5_partition {X : Type*} (U : Set (X → ℝ)) (F : Set (↥U → ℝ))
    (G : Set (↥U → Bool)) (k dG N : ℕ)
    (hdec : PiecewiseDecomposable (dual U) F G k) (hG : HasVCDim (dualB G) dG)
    (hk : 1 ≤ k) (hN : 1 ≤ N) (x : Fin N → X) :
    ∃ (M : ℕ) (cell : ↥U → Fin M), Function.Surjective cell ∧
      (M : ℝ) ≤ (Real.exp 1 * k * N) ^ dG ∧ (1 ≤ dG → (M : ℝ) < (Real.exp 1 * k * N) ^ dG) ∧
      ∀ j : Fin M, ∃ f : Fin N → ↥U → ℝ, (∀ i, f i ∈ F) ∧
        ∀ u : ↥U, cell u = j → ∀ i, (u : X → ℝ) (x i) = f i u := by sorry

end BalcanDDA.Piecewise
