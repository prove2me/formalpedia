-- Prove2me | Theorems.Thm_BBCode_two_gross_params
-- name    : BBCode.two_gross_params
-- status  : Open
-- author  : @Winningatmath
-- created : 2026-10-16T17:59:55.658983+00:00
-- url     : https://prove2.me/theorems/1f4ac1e2-96ce-49f9-9d13-0f089e40766e
-- title:
--   Table 3 — two-gross code $[[288,12,18]]$
-- statement:
--   The two-gross code of Bravyi et al.
--
--   Let $G=\mathbb Z_{12}\times\mathbb Z_{12}$ and let
--   $$A=x^{3}+y^{2}+y^{7},\qquad B=y^{3}+x+x^{2}$$
--   in $\mathbb F_2[x,y]/(x^{12}-1,\,y^{12}-1)$. The bivariate-bicycle code with check matrices $H_X=[A\mid B]$ and $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$ is an
--   $$[[288,12,18]]$$
--   code in both sectors:
--
--   1. it acts on $n=288=2\cdot12\cdot12$ qubits;
--   2. it encodes $k=12$ logical qubits: $\operatorname{rank}_{\mathbb F_2}H_X+\operatorname{rank}_{\mathbb F_2}H_Z+12=288$;
--   3. its X-distance is exactly $18$: some $v$ with $H_Zv=0$ and $v\notin\operatorname{row}(H_X)$ has weight $18$, and every such $v$ has weight at least $18$;
--   4. its Z-distance is exactly $18$ (dually, with $H_X$ and $H_Z$ exchanged).
--
--   **Formalization Note** Polynomials are `Finset`s of monomials $(i,j)$ in `ZMod l × ZMod m`; `IsCode A B n k d` is defined in `BBCode_Setting`.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, Table 3 (p. 5); polynomials from Bravyi et al., Nature 627, 778 (2024), Table 3, https://doi.org/10.1038/s41586-024-07107-7

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem two_gross_params :
    IsCode (l := 12) (m := 12) {(3, 0), (0, 2), (0, 7)} {(0, 3), (1, 0), (2, 0)} 288 12 18 := by
  sorry

end BBCode
