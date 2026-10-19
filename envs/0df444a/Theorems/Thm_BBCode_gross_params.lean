-- Prove2me | Theorems.Thm_BBCode_gross_params
-- name    : BBCode.gross_params
-- status  : Proved
-- author  : @Winningatmath
-- created : 2026-10-16T17:59:30.897337+00:00
-- url     : https://prove2.me/theorems/85b4ba28-096b-483e-bba6-bcd3776c6945
-- title:
--   Table 3 — gross code $[[144,12,12]]$
-- statement:
--   The gross code of Bravyi et al.
--
--   Let $G=\mathbb Z_{12}\times\mathbb Z_{6}$ and let
--   $$A=x^{3}+y+y^{2},\qquad B=y^{3}+x+x^{2}$$
--   in $\mathbb F_2[x,y]/(x^{12}-1,\,y^{6}-1)$. The bivariate-bicycle code with check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ is an
--   $$[[144,12,12]]$$
--   code in both sectors:
--
--   1. it acts on $n=144=2\cdot12\cdot6$ qubits;
--   2. it encodes $k=12$ logical qubits: $\operatorname{rank}_{\mathbb F_2}H_X+\operatorname{rank}_{\mathbb F_2}H_Z+12=144$;
--   3. its X-distance is exactly $12$: some $v$ with $H_Zv=0$ and $v\notin\operatorname{row}(H_X)$ has weight $12$, and every such $v$ has weight at least $12$;
--   4. its Z-distance is exactly $12$ (dually, with $H_X$ and $H_Z$ exchanged).
--
--   **Formalization Note** Polynomials are `Finset`s of monomials $(i,j)$ in `ZMod l × ZMod m`; `IsCode A B n k d` is defined in `BBCode_Setting`.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, Table 3 (p. 5); polynomials from Bravyi et al., Nature 627, 778 (2024), Table 3, https://doi.org/10.1038/s41586-024-07107-7

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem gross_params :
    IsCode (l := 12) (m := 6) {(3, 0), (0, 1), (0, 2)} {(0, 3), (1, 0), (2, 0)} 144 12 12 := by
  sorry

end BBCode
