-- Prove2me | Theorems.Thm_BBCode_bb108_params
-- name    : BBCode.bb108_params
-- status  : Proved
-- author  : @Winningatmath
-- created : 2026-10-16T17:59:02.645832+00:00
-- url     : https://prove2.me/theorems/83bbd82b-72f2-4573-a7ff-543758c716dd
-- title:
--   Table 3 — $[[108,8,10]]$ (Bravyi et al. ladder)
-- statement:
--   The $[[108,8,10]]$ bivariate-bicycle code of Bravyi et al.
--
--   Let $G=\mathbb Z_{9}\times\mathbb Z_{6}$ and let
--   $$A=x^{3}+y+y^{2},\qquad B=y^{3}+x+x^{2}$$
--   in $\mathbb F_2[x,y]/(x^{9}-1,\,y^{6}-1)$. The bivariate-bicycle code with check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ is an
--   $$[[108,8,10]]$$
--   code in both sectors:
--
--   1. it acts on $n=108=2\cdot9\cdot6$ qubits;
--   2. it encodes $k=8$ logical qubits: $\operatorname{rank}_{\mathbb F_2}H_X+\operatorname{rank}_{\mathbb F_2}H_Z+8=108$;
--   3. its X-distance is exactly $10$: some $v$ with $H_Zv=0$ and $v\notin\operatorname{row}(H_X)$ has weight $10$, and every such $v$ has weight at least $10$;
--   4. its Z-distance is exactly $10$ (dually, with $H_X$ and $H_Z$ exchanged).
--
--   **Formalization Note** Polynomials are `Finset`s of monomials $(i,j)$ in `ZMod l × ZMod m`; `IsCode A B n k d` is defined in `BBCode_Setting`.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, Table 3 (p. 5); polynomials from Bravyi et al., Nature 627, 778 (2024), Table 3, https://doi.org/10.1038/s41586-024-07107-7

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem bb108_params :
    IsCode (l := 9) (m := 6) {(3, 0), (0, 1), (0, 2)} {(0, 3), (1, 0), (2, 0)} 108 8 10 := by sorry

end BBCode
