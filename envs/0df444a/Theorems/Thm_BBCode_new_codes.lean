-- Prove2me | Theorems.Thm_BBCode_new_codes
-- name    : BBCode.new_codes
-- status  : Proved
-- author  : @Winningatmath
-- created : 2026-10-16T18:02:40.015346+00:00
-- url     : https://prove2.me/theorems/be811417-3b18-401a-b3ff-8e34bf48227a
-- title:
--   Three new weight-6 BB codes: two $[[336,20,12]]$ and one $[[360,24,12]]$
-- statement:
--   The three bivariate-bicycle codes of Table 9 have the stated parameters, with $d_X=d_Z=12$:
--
--   1. over $\mathbb Z_2\times\mathbb Z_{84}$, $A=1+y+xy^{5}$, $B=1+y^{4}+y^{62}$: $[[336,20,12]]$;
--   2. over $\mathbb Z_2\times\mathbb Z_{84}$, $A=1+y+xy^{5}$, $B=1+y^{20}+y^{46}$: $[[336,20,12]]$;
--   3. over $\mathbb Z_6\times\mathbb Z_{30}$, $A=1+y+xy^{2}$, $B=1+y^{8}+x^{2}y^{16}$: $[[360,24,12]]$.
--
--   Here $H_X=[A\mid B]$, $H_Z=[B^{\mathsf T}\mid A^{\mathsf T}]$, $$k=n-\operatorname{rank}H_X-\operatorname{rank}H_Z,$$ and each distance is the minimum weight of a nontrivial logical in that sector. These codes encode 25% and 50% more logical qubits than the best distance-12 weight-6 code previously reported.
--
--   **Formalization Note** `IsCode` is defined in `BBCode_Setting`.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, Table 9 (p. 15) and Table 3 (p. 5)

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem new_codes :
    IsCode (l := 2) (m := 84) {(0, 0), (0, 1), (1, 5)} {(0, 0), (0, 4), (0, 62)} 336 20 12 ∧
    IsCode (l := 2) (m := 84) {(0, 0), (0, 1), (1, 5)} {(0, 0), (0, 20), (0, 46)} 336 20 12 ∧
    IsCode (l := 6) (m := 30) {(0, 0), (0, 1), (1, 2)} {(0, 0), (0, 8), (2, 16)} 360 24 12 := by
  sorry

end BBCode
