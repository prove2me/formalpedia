-- Prove2me | Theorems.Thm_BBCode_new336_class2_params
-- name    : BBCode.new336_class2_params
-- status  : Proved
-- author  : @Winningatmath
-- created : 2026-10-16T18:01:18.842393+00:00
-- url     : https://prove2.me/theorems/c1c39db9-186d-4fcc-8fd4-0507b8f1f0d0
-- title:
--   Table 9 — new $[[336,20,12]]$ code, class 2
-- statement:
--   New bivariate-bicycle code, class 2 of the two $[[336,20,12]]$ symmetry classes.
--
--   Let $G=\mathbb Z_{2}\times\mathbb Z_{84}$ and let
--   $$A=1+y+xy^{5},\qquad B=1+y^{20}+y^{46}$$
--   in $\mathbb F_2[x,y]/(x^{2}-1,\,y^{84}-1)$. The bivariate-bicycle code with check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ is an
--   $$[[336,20,12]]$$
--   code in both sectors:
--
--   1. it acts on $n=336=2\cdot2\cdot84$ qubits;
--   2. it encodes $k=20$ logical qubits: $\operatorname{rank}_{\mathbb F_2}H_X+\operatorname{rank}_{\mathbb F_2}H_Z+20=336$;
--   3. its X-distance is exactly $12$: some $v$ with $H_Zv=0$ and $v\notin\operatorname{row}(H_X)$ has weight $12$, and every such $v$ has weight at least $12$;
--   4. its Z-distance is exactly $12$ (dually, with $H_X$ and $H_Z$ exchanged).
--
--   **Formalization Note** Polynomials are `Finset`s of monomials $(i,j)$ in `ZMod l × ZMod m`; `IsCode A B n k d` is defined in `BBCode_Setting`.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, Table 3 (p. 5); polynomials from Table 9 (p. 15)

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem new336_class2_params :
    IsCode (l := 2) (m := 84) {(0, 0), (0, 1), (1, 5)} {(0, 0), (0, 20), (0, 46)} 336 20 12 := by
  sorry

end BBCode
