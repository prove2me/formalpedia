-- Prove2me | Theorems.Thm_BBCode_bb360_params
-- name    : BBCode.bb360_params
-- status  : Open
-- author  : @Winningatmath
-- created : 2026-10-16T18:00:27.354257+00:00
-- url     : https://prove2.me/theorems/5c3ef584-9301-484d-aeb0-09b503c26c1b
-- title:
--   Table 3 and §5 — $[[360,12,24]]$: exact distance 24
-- statement:
--   The $[[360,12]]$ bivariate-bicycle code of Bravyi et al., for which only $d\le 24$ had been reported; the source establishes $d_X=d_Z=24$.
--
--   Let $G=\mathbb Z_{30}\times\mathbb Z_{6}$ and let
--   $$A=x^{9}+y+y^{2},\qquad B=y^{3}+x^{25}+x^{26}$$
--   in $\mathbb F_2[x,y]/(x^{30}-1,\,y^{6}-1)$. The bivariate-bicycle code with check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ is an
--   $$[[360,12,24]]$$
--   code in both sectors:
--
--   1. it acts on $n=360=2\cdot30\cdot6$ qubits;
--   2. it encodes $k=12$ logical qubits: $\operatorname{rank}_{\mathbb F_2}H_X+\operatorname{rank}_{\mathbb F_2}H_Z+12=360$;
--   3. its X-distance is exactly $24$: some $v$ with $H_Zv=0$ and $v\notin\operatorname{row}(H_X)$ has weight $24$, and every such $v$ has weight at least $24$;
--   4. its Z-distance is exactly $24$ (dually, with $H_X$ and $H_Z$ exchanged).
--
--   **Formalization Note** Polynomials are `Finset`s of monomials $(i,j)$ in `ZMod l × ZMod m`; `IsCode A B n k d` is defined in `BBCode_Setting`.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, §5 (p. 4) and Table 3 (p. 5); polynomials from Bravyi et al., Nature 627, 778 (2024), Table 3, https://doi.org/10.1038/s41586-024-07107-7

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem bb360_params :
    IsCode (l := 30) (m := 6) {(9, 0), (0, 1), (0, 2)} {(0, 3), (25, 0), (26, 0)} 360 12 24 := by
  sorry

end BBCode
