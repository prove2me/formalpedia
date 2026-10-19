-- Prove2me | Theorems.Thm_BBCode_bb90_params
-- name    : BBCode.bb90_params
-- status  : Proved
-- author  : @Winningatmath
-- created : 2026-10-16T17:58:36.671996+00:00
-- url     : https://prove2.me/theorems/e491800e-3a2d-495c-be6c-6bc424c272e7
-- title:
--   Table 3 — $[[90,8,10]]$ (Bravyi et al. ladder)
-- statement:
--   The $[[90,8,10]]$ bivariate-bicycle code of Bravyi et al.
--
--   Let $G=\mathbb Z_{15}\times\mathbb Z_{3}$ and let
--   $$A=x^{9}+y+y^{2},\qquad B=1+x^{2}+x^{7}$$
--   in $\mathbb F_2[x,y]/(x^{15}-1,\,y^{3}-1)$. The bivariate-bicycle code with check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ is an
--   $$[[90,8,10]]$$
--   code in both sectors:
--
--   1. it acts on $n=90=2\cdot15\cdot3$ qubits;
--   2. it encodes $k=8$ logical qubits: $\operatorname{rank}_{\mathbb F_2}H_X+\operatorname{rank}_{\mathbb F_2}H_Z+8=90$;
--   3. its X-distance is exactly $10$: some $v$ with $H_Zv=0$ and $v\notin\operatorname{row}(H_X)$ has weight $10$, and every such $v$ has weight at least $10$;
--   4. its Z-distance is exactly $10$ (dually, with $H_X$ and $H_Z$ exchanged).
--
--   **Formalization Note** Polynomials are `Finset`s of monomials $(i,j)$ in `ZMod l × ZMod m`; `IsCode A B n k d` is defined in `BBCode_Setting`.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, Table 3 (p. 5); polynomials from Bravyi et al., Nature 627, 778 (2024), Table 3, https://doi.org/10.1038/s41586-024-07107-7

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem bb90_params :
    IsCode (l := 15) (m := 3) {(9, 0), (0, 1), (0, 2)} {(0, 0), (2, 0), (7, 0)} 90 8 10 := by sorry

end BBCode
