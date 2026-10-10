-- Prove2me | Theorems.Thm_BookProof_ChapterParityQL_QLParity_order_four
-- name    : BookProof.ChapterParityQL.QLParity_order_four
-- status  : Open
-- author  : @leonardopedro
-- created : 2026-10-10T09:09:23.534975+00:00
-- url     : https://prove2.me/theorems/831da27c-1b59-405d-80c2-5896e3cf0cba
-- title:
--   `BookProof.ChapterParityQL.QLParity_order_four` : QLParity * QLParity ≠ 1 ∧ QLParity * QLParity * (QLParity * QLParity) = 1
-- statement:
--   Prove the following Lean 4 theorem from `ChapterParityQL`.
--
--   `BookProof.ChapterParityQL.QLParity_order_four` : QLParity * QLParity ≠ 1 ∧ QLParity * QLParity * (QLParity * QLParity) = 1
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterParityQL.QLParity_order_four`.

-- Generated from ChapterParityQL.lean — theorem BookProof.ChapterParityQL.QLParity_order_four
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterParity
import Mathlib
import Definitions.Def_ChapterParityQL
open BookProof.ChapterParityQL


open Matrix
open scoped Kronecker


open BookProof.ChapterA3
open BookProof.ChapterParity

theorem BookProof.ChapterParityQL.QLParity_order_four :
    QLParity * QLParity ≠ 1 ∧
      QLParity * QLParity * (QLParity * QLParity) = 1 := by sorry
