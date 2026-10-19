-- Prove2me | Theorems.Thm_BBCode_new360_params
-- name    : BBCode.new360_params
-- status  : Proved
-- author  : @Winningatmath
-- created : 2026-10-16T18:01:49.797139+00:00
-- url     : https://prove2.me/theorems/5cfa9063-07f8-4665-9813-ea43082ce94a
-- title:
--   Table 9 — new $[[360,24,12]]$ code
-- statement:
--   New bivariate-bicycle code with 24 logical qubits.
--
--   Let $G=\mathbb Z_{6}\times\mathbb Z_{30}$ and let
--   $$A=1+y+xy^{2},\qquad B=1+y^{8}+x^{2}y^{16}$$
--   in $\mathbb F_2[x,y]/(x^{6}-1,\,y^{30}-1)$. The bivariate-bicycle code with check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ is an
--   $$[[360,24,12]]$$
--   code in both sectors:
--
--   1. it acts on $n=360=2\cdot6\cdot30$ qubits;
--   2. it encodes $k=24$ logical qubits: $\operatorname{rank}_{\mathbb F_2}H_X+\operatorname{rank}_{\mathbb F_2}H_Z+24=360$;
--   3. its X-distance is exactly $12$: some $v$ with $H_Zv=0$ and $v\notin\operatorname{row}(H_X)$ has weight $12$, and every such $v$ has weight at least $12$;
--   4. its Z-distance is exactly $12$ (dually, with $H_X$ and $H_Z$ exchanged).
--
--   **Formalization Note** Polynomials are `Finset`s of monomials $(i,j)$ in `ZMod l × ZMod m`; `IsCode A B n k d` is defined in `BBCode_Setting`.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, Table 3 (p. 5); polynomials from Table 9 (p. 15)

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem new360_params :
    IsCode (l := 6) (m := 30) {(0, 0), (0, 1), (1, 2)} {(0, 0), (0, 8), (2, 16)} 360 24 12 := by
  sorry

end BBCode
