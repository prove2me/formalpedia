-- Prove2me | Theorems.Thm_BookProof_ChapterMajoranaProp74_majoranaFourier_prop74
-- name    : BookProof.ChapterMajoranaProp74.majoranaFourier_prop74
-- status  : Proved
-- author  : @leonardopedro
-- created : 2026-10-09T12:57:50.752102+00:00
-- url     : https://prove2.me/theorems/ae91989e-3de3-4826-8643-162a4bcce125
-- title:
--   `BookProof.ChapterMajoranaProp74.majoranaFourier_prop74` (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q) (n : Fin 3 → ℝ) (hn : ∑ i, (n i) ^ 2 = 1) : Qmat (dgamma 0) (nslash n) m q * Sinv (Aop
-- statement:
--   Prove the following Lean 4 theorem from `ChapterMajoranaProp74`.
--
--   `BookProof.ChapterMajoranaProp74.majoranaFourier_prop74` (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q) (n : Fin 3 → ℝ) (hn : ∑ i, (n i) ^ 2 = 1) : Qmat (dgamma 0) (nslash n) m q * Sinv (Aop n) (boostC m q) (boostS m q) = Sinv (Aop n) (boostC m q) (boostS m q) * Rmat (dgamma 0) (Ep m q)
--
--   Formalization note: Lean 4 identifier `BookProof.ChapterMajoranaProp74.majoranaFourier_prop74`.

-- Generated from ChapterMajoranaProp74.lean — theorem BookProof.ChapterMajoranaProp74.majoranaFourier_prop74
import Mathlib
import Definitions.Def_ChapterMajoranaProp74
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterMajoranaFourier
open BookProof.ChapterA3
open BookProof.ChapterMajoranaFourier
open BookProof.ChapterMajoranaProp74


open Matrix


open BookProof.ChapterMajoranaFourier
open BookProof.ChapterA3

theorem BookProof.ChapterMajoranaProp74.majoranaFourier_prop74 (m q : ℝ) (hm : 0 ≤ m) (hq : 0 < q)
    (n : Fin 3 → ℝ) (hn : ∑ i, (n i) ^ 2 = 1) :
    Qmat (dgamma 0) (nslash n) m q * Sinv (Aop n) (boostC m q) (boostS m q)
      = Sinv (Aop n) (boostC m q) (boostS m q) * Rmat (dgamma 0) (Ep m q) := by sorry
