-- Prove2me | Theorems.Thm_EditGV897_Main_partial_row_semantics
-- name    : EditGV897.Main.partial_row_semantics
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T02:47:38.698981+00:00
-- url     : https://prove2.me/theorems/1da189d2-19d2-423a-82c8-ee5a8b6d1cb2
-- title:
--   Exact partial-row expectations and deterministic witness halving
-- statement:
--   For every affine binary equation list, the prescribed Gaussian routine counts its solution set exactly. For each legal affine edit family $F$ and current row list $G$ in Lemma 1, the executable witness count is exact on every affine candidate set. For every row prefix $p$ of length at most $n$, the integer evaluator satisfies
--
--   $$\operatorname{twiceExpectation}(F,G,p)=2\,\mathbb E_{h\text{ extending }p}[W_{G\cup\{h\}}(\mathbb F_2^n)].$$
--
--   The prescribed minimizing-prefix row construction consequently satisfies
--
--   $$2W_{G\cup\{h\}}(\mathbb F_2^n)\le W_G(\mathbb F_2^n).$$
--
--   These are the exact counting and halving assertions of Lemma 1. The average is over actual row completions, and the finite-program runtime obligations are separate from this statement.
-- source:
--   Gabrys, Singhvi, Yaakobi, Making Every Edit Count, STOC 2027 submission #897, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/897.pdf, §3.2 and §4.1, equation (10), Lemma 1 and its proof, printed pp.8–10 / PDF pp.9–11

import Definitions.Def_EditGV897_Main_Construction
open EditGV897.Main

theorem EditGV897.Main.partial_row_semantics :
    (∀ (n : ℕ) (E : List (Equation n)), affineCount E = (affineSet E).card) ∧
    (∀ (n t : ℕ) (F : Family n) (G : Rows n),
      1 ≤ t → EditFamily t F → G.length ≤ n →
      (∀ E : List (Equation n), witnessCount F G E = witnessSum F G (affineSet E)) ∧
      (∀ p : List Bit, p.length ≤ n → (twiceExpectation F G p : ℚ) = 2 * expectation F G p) ∧
      2 * witnessSum F (G ++ [chooseRow F G]) Finset.univ ≤ witnessSum F G Finset.univ) := by sorry
