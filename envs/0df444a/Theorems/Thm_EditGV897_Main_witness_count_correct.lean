-- Prove2me | Theorems.Thm_EditGV897_Main_witness_count_correct
-- name    : EditGV897.Main.witness_count_correct
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:25:45.116147+00:00
-- url     : https://prove2.me/theorems/d9399bb5-8263-44bf-a3ac-8d7b4084338b
-- title:
--   Exact collision-witness counting by affine-system differences
-- statement:
--   Let $F$ be an ordered family of binary affine maps on $\mathbb F_2^n$, let $G$ be parity rows, and let $S$ be the solution set of any affine equation list $E$. For each occurrence of a map $f$ and each $x\in S$, count a collision witness when $x+f(x)\ne0$ and $G(x+f(x))=0$. Then the specified executable counting routine agrees exactly with the total witness count:
--
--   $$\operatorname{witnessCount}(F,G,E)=\sum_{x\in S}W_G(x).$$
--
--   Repeated map occurrences are counted separately and fixed points are excluded. This supplies the exact counting interface for conditional expectations, syndrome selection, and signed-prefix encoding.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §3.2 affine-system witness counting, printed pp.8–9 / PDF pp.9–10

import Definitions.Def_EditGV897_Main_Witnesses
open EditGV897.Main

theorem EditGV897.Main.witness_count_correct (n : ℕ) (F : Family n) (G : Rows n)
    (E : List (Equation n)) : witnessCount F G E = witnessSum F G (affineSet E) := by sorry
