-- Prove2me | Theorems.Thm_BalcanDDA_Piecewise_lemma3_4_dual_sauer
-- name    : BalcanDDA.Piecewise.lemma3_4_dual_sauer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-04T06:16:08.094337+00:00
-- url     : https://prove2.me/theorems/da29de98-cc41-4cde-b13d-28b4058a27e0
-- title:
--   Lemma 3.4 — $|\{(h_1(y),\dots,h_N(y)) \mid y \in \mathcal Y\}| \le (eN)^{\mathrm{VCdim}(\mathcal H^*)}$
-- statement:
--   Let $\mathcal H$ be a set of functions from a domain $\mathcal Y$ to $\{0,1\}$, and suppose its dual class $\mathcal H^*$ has VC-dimension $d$. Let $N \ge 1$ and let $h_1, \dots, h_N \in \mathcal H$ (repetitions allowed). Then the number of distinct binary vectors obtained by evaluating $h_1, \dots, h_N$ at a common input is bounded by
--   $$\bigl|\{\, (h_1(y), \dots, h_N(y)) \mid y \in \mathcal Y \,\}\bigr| \le (eN)^{d}.$$
--
--   The bound depends on the VC-dimension of the dual class, not of $\mathcal H$: it counts the regions into which $N$ fixed boundary functions cut the domain. It is used twice in the proof of Theorem 3.3, once for boundary functions and once (through a thresholding argument) for piece functions.
--
--   **Formalization Note.** The count is the cardinality (`Set.ncard`) of a subset of $\{0,1\}^N$, which is finite. $N \ge 1$ is added as a correction of the printed statement: at $N = 0$ the left side is $1$ while $(e\cdot 0)^d = 0$ for $d \ge 1$. The VC-dimension is the published exact-value predicate `HasVCDim` applied to the Boolean dual class, whose domain is the class $\mathcal H$ as a subtype.
-- source:
--   Balcan et al., How Much Data Is Sufficient to Learn High-Performing Algorithms?, arXiv:1908.02894v4, p. 8, Lemma 3.4, Eq. (4)

import Mathlib
import Definitions.Def_FoundationsML_RademacherVC_GrowthFunction
import Definitions.Def_FoundationsML_RademacherVC_HasVCDim
import Definitions.Def_BalcanDDA_Piecewise_dual

open FoundationsML.RademacherVC

namespace BalcanDDA.Piecewise

/-- Lemma 3.4 (Balcan et al., arXiv:1908.02894v4, p. 8). Let `H` be a set of functions
`Y → {0,1}` whose dual class has VC-dimension `d`. For any `h₁, …, h_N ∈ H` (`N ≥ 1`), the
number of binary vectors `(h₁(y), …, h_N(y))` obtained as `y` ranges over `Y` is at most
`(eN)^d`. Correction: `N ≥ 1` is added (at `N = 0` the printed bound reads `1 ≤ 0`). -/
theorem lemma3_4_dual_sauer {Y : Type*} (H : Set (Y → Bool)) (d N : ℕ)
    (hH : HasVCDim (dualB H) d) (hN : 1 ≤ N)
    (h : Fin N → Y → Bool) (hmem : ∀ i, h i ∈ H) :
    ((Set.range fun y : Y => fun i => h i y).ncard : ℝ) ≤ (Real.exp 1 * N) ^ d := by sorry

end BalcanDDA.Piecewise
