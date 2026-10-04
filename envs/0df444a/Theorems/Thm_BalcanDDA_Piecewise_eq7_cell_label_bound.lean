-- Prove2me | Theorems.Thm_BalcanDDA_Piecewise_eq7_cell_label_bound
-- name    : BalcanDDA.Piecewise.eq7_cell_label_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:16:27.863678+00:00
-- url     : https://prove2.me/theorems/ef2fee08-5620-4068-aaea-9e82cd0865b9
-- title:
--   Bound on Eq. (7): piece functions label $N$ points in at most $(eN)^{\mathrm{Pdim}(\mathcal F^*)}$ ways
-- statement:
--   Let $\mathcal U \subseteq \mathbb R^{\mathcal X}$ and let $\mathcal F \subseteq \mathbb R^{\mathcal U}$ be a class of piece functions whose dual class has pseudo-dimension $\mathrm{Pdim}(\mathcal F^*) = d_F$. Let $N \ge 1$, let $f_1, \dots, f_N \in \mathcal F$ (repetitions allowed), let $z_1, \dots, z_N \in \mathbb R$ be targets, and let $S \subseteq \mathcal U$ be any set (in the proof, a cell of the partition from Claim 3.5). Then
--   $$\Bigl|\bigl\{\, \bigl(\mathbb 1[f_1(u) > z_1], \dots, \mathbb 1[f_N(u) > z_N]\bigr) \;\bigm|\; u \in S \,\bigr\}\Bigr| \le (eN)^{d_F}.$$
--
--   This is the second step of the proof of Theorem 3.3: on a cell where the dual functions coincide with fixed piece functions, the utility functions can label $x_1, \dots, x_N$ relative to the targets in at most $(eN)^{\mathrm{Pdim}(\mathcal F^*)}$ ways.
--
--   **Formalization Note.** The paper's sign vector $(\mathrm{sign}(f_i(u) - z_i))_i$ is read as the Boolean vector $(\mathbb 1[z_i < f_i(u)])_i$, the same strict-threshold convention used by the published `Shatters` predicate, so that the count equals $2^N$ exactly on a shattered tuple. The count is the cardinality of a subset of $\{0,1\}^N$.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 9, proof of Theorem 3.3, Eq. (7) and the sentence after it

import Mathlib
import Definitions.Def_FoundationsML_Regression_Shatters
import Definitions.Def_FoundationsML_Regression_PseudoDim
import Definitions.Def_BalcanDDA_Piecewise_dual

open FoundationsML.Regression

namespace BalcanDDA.Piecewise

/-- The bound on Equation (7) (Balcan et al., arXiv:1908.02894v4, p. 9, proof of Theorem 3.3,
sentence after (7)). If `Pdim(F*) = dF`, then for any piece functions `f₁, …, f_N ∈ F`
(`N ≥ 1`), targets `z₁, …, z_N` and any set `S ⊆ U` (a cell of the partition), the
functions `u ∈ S` produce at most `(eN)^{dF}` label vectors `(I{f₁(u) > z₁}, …, I{f_N(u) > z_N})`. -/
theorem eq7_cell_label_bound {X : Type*} (U : Set (X → ℝ)) (F : Set (↥U → ℝ)) (dF N : ℕ)
    (hF : PseudoDim (dual F) dF) (hN : 1 ≤ N)
    (f : Fin N → ↥U → ℝ) (hf : ∀ i, f i ∈ F) (z : Fin N → ℝ) (S : Set ↥U) :
    (((fun u i => decide (z i < f i u)) '' S).ncard : ℝ) ≤ (Real.exp 1 * N) ^ dF := by sorry

end BalcanDDA.Piecewise
