-- Prove2me | Theorems.Thm_EditGV897_Main_affine_count_correct
-- name    : EditGV897.Main.affine_count_correct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:20:49.271423+00:00
-- url     : https://prove2.me/theorems/cff3f41c-2b76-4312-a242-cf7abfc557c3
-- title:
--   Exact cardinality from binary Gaussian elimination
-- statement:
--   Let $E$ be any finite ordered list of affine equations over $\mathbb F_2$ in $n$ binary variables. The prescribed Gaussian-elimination counting routine returns exactly the number of satisfying words:
--
--   $$\operatorname{affineCount}(E)=\left|\left\{x\in\mathbb F_2^n:\langle a,x\rangle=b\text{ for every }(a,b)\in E\right\}\right|.$$
--
--   This includes inconsistent systems, repeated or zero equations, and zero-dimensional systems. It provides the exact affine-system counting interface used for collision-witness evaluation and signed-prefix indexing.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §3.2 affine-system counting and Lemma 1, printed pp.8–10 / PDF pp.9–11

import Definitions.Def_EditGV897_Main_Witnesses
open EditGV897.Main

theorem EditGV897.Main.affine_count_correct (n : ℕ) (E : List (Equation n)) : affineCount E = (affineSet E).card := by sorry
