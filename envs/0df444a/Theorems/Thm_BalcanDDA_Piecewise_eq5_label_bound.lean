-- Prove2me | Theorems.Thm_BalcanDDA_Piecewise_eq5_label_bound
-- name    : BalcanDDA.Piecewise.eq5_label_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:17:00.502165+00:00
-- url     : https://prove2.me/theorems/0b445919-c2e4-493f-b7ee-7ac22c1f8d94
-- title:
--   Bound on Eq. (5): $\mathcal U$ labels $N$ points in at most $(ekN)^{\mathrm{VCdim}(\mathcal G^*)}(eN)^{\mathrm{Pdim}(\mathcal F^*)}$ ways
-- statement:
--   Let $\mathcal U \subseteq \mathbb R^{\mathcal X}$ be a class whose dual class $\mathcal U^*$ is $(\mathcal F, \mathcal G, k)$-piecewise decomposable, with $\mathcal G \subseteq \{0,1\}^{\mathcal U}$, $\mathcal F \subseteq \mathbb R^{\mathcal U}$, $k \ge 1$, $\mathrm{Pdim}(\mathcal F^*) = d_F$ and $\mathrm{VCdim}(\mathcal G^*) = d_G$. For every $N \ge 1$, instances $x_1, \dots, x_N \in \mathcal X$ and targets $z_1, \dots, z_N \in \mathbb R$,
--   $$\Bigl|\bigl\{\, \bigl(\mathbb 1[u(x_1) > z_1], \dots, \mathbb 1[u(x_N) > z_N]\bigr) \;\bigm|\; u \in \mathcal U \,\bigr\}\Bigr| \le (ekN)^{d_G}\,(eN)^{d_F}.$$
--
--   This bounds the number of ways the class $\mathcal U$ can label $N$ problem instances relative to target thresholds, the quantity in Equation (5) of the paper, and is the heart of the pseudo-dimension bound of Theorem 3.3.
--
--   **Formalization Note.** The paper's sign vectors over $\rho \in \mathcal P$ are counted here over $u \in \mathcal U$ (the same set of vectors), read as Boolean vectors $(\mathbb 1[z_i < u(x_i)])_i$, matching the strict-threshold convention of the published `Shatters` predicate. $k \ge 1$ and $N \ge 1$ are made explicit.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 9, proof of Theorem 3.3 (display (5) on p. 8)

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_FoundationsML_Regression_PseudoDim
import Definitions.Def_FoundationsML_RademacherVC_GrowthFunction
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim
import Definitions.Def_BalcanDDA_Piecewise_dual
import Definitions.Def_BalcanDDA_Piecewise_PiecewiseDecomposable

open FoundationsML.Regression FoundationsML.RademacherVC

namespace BalcanDDA.Piecewise

/-- The bound on Equation (5) (Balcan et al., arXiv:1908.02894v4, p. 9, proof of Theorem 3.3;
display (5) on p. 8). If `U*` is `(F, G, k)`-piecewise decomposable, `Pdim(F*) = dF`,
`VCdim(G*) = dG`, `k ≥ 1` and `N ≥ 1`, then for any instances `x₁, …, x_N` and targets
`z₁, …, z_N`, the class `U` produces at most `(ekN)^{dG} (eN)^{dF}` label vectors
`(I{u(x₁) > z₁}, …, I{u(x_N) > z_N})`. -/
theorem eq5_label_bound {X : Type*} (U : Set (X → ℝ)) (F : Set (↥U → ℝ))
    (G : Set (↥U → Bool)) (k dF dG N : ℕ)
    (hdec : PiecewiseDecomposable (dual U) F G k)
    (hF : PseudoDim (dual F) dF) (hG : HasVCDim (dualB G) dG)
    (hk : 1 ≤ k) (hN : 1 ≤ N) (x : Fin N → X) (z : Fin N → ℝ) :
    ((Set.range fun u : ↥U => fun i => decide (z i < (u : X → ℝ) (x i))).ncard : ℝ) ≤
      (Real.exp 1 * k * N) ^ dG * (Real.exp 1 * N) ^ dF := by sorry

end BalcanDDA.Piecewise
