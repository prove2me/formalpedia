-- Prove2me | Theorems.Thm_BalcanDDA_Piecewise_shatter_two_pow_bound
-- name    : BalcanDDA.Piecewise.shatter_two_pow_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:17:04.887052+00:00
-- url     : https://prove2.me/theorems/ddb72dad-f2e8-480f-af27-3f2b16005f52
-- title:
--   Shattering inequality $2^N \le (ekN)^{\mathrm{VCdim}(\mathcal G^*)}(eN)^{\mathrm{Pdim}(\mathcal F^*)}$
-- statement:
--   Under the hypotheses of Theorem 3.3 — the dual class $\mathcal U^*$ is $(\mathcal F, \mathcal G, k)$-piecewise decomposable with $k \ge 1$, $\mathrm{Pdim}(\mathcal F^*) = d_F$ and $\mathrm{VCdim}(\mathcal G^*) = d_G$ — if $\mathcal U$ shatters problem instances $x_1, \dots, x_N$ with $N \ge 1$ (that is, for some targets $z_1, \dots, z_N$ all $2^N$ above/below patterns are realized by functions in $\mathcal U$), then
--   $$2^N \le (ekN)^{d_G}\,(eN)^{d_F}.$$
--
--   Hence the pseudo-dimension of $\mathcal U$ is at most the largest $N$ satisfying this inequality, which is what Theorem 3.3 bounds explicitly.
--
--   **Formalization Note.** Shattering is the published `Shatters` predicate (strict thresholds, $u(x_i) > z_i$); see the note on the pseudo-dimension reference for why this matches the paper's sign convention. $N \ge 1$ is needed: at $N = 0$ the right side is $0$ when $d_F + d_G \ge 1$.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 9, proof of Theorem 3.3

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_FoundationsML_Regression_PseudoDim
import Definitions.Def_FoundationsML_RademacherVC_GrowthFunction
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim
import Definitions.Def_BalcanDDA_Piecewise_dual
import Definitions.Def_BalcanDDA_Piecewise_PiecewiseDecomposable

open FoundationsML.Regression FoundationsML.RademacherVC

namespace BalcanDDA.Piecewise

/-- The shattering inequality (Balcan et al., arXiv:1908.02894v4, p. 9, proof of Theorem 3.3).
If `U*` is `(F, G, k)`-piecewise decomposable, `Pdim(F*) = dF`, `VCdim(G*) = dG`, `k ≥ 1`,
`N ≥ 1`, and `U` shatters `x₁, …, x_N`, then `2^N ≤ (ekN)^{dG} (eN)^{dF}`. -/
theorem shatter_two_pow_bound {X : Type*} (U : Set (X → ℝ)) (F : Set (↥U → ℝ))
    (G : Set (↥U → Bool)) (k dF dG N : ℕ)
    (hdec : PiecewiseDecomposable (dual U) F G k)
    (hF : PseudoDim (dual F) dF) (hG : HasVCDim (dualB G) dG)
    (hk : 1 ≤ k) (hN : 1 ≤ N) (x : Fin N → X) (hsh : Shatters U x) :
    (2 : ℝ) ^ N ≤ (Real.exp 1 * k * N) ^ dG * (Real.exp 1 * N) ^ dF := by sorry

end BalcanDDA.Piecewise
