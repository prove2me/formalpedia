-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_support_deficit_cell_bound
-- name    : BirthdayEntropy.Soundness.support_deficit_cell_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-11-18T01:12:29.180736+00:00
-- url     : https://prove2.me/theorems/0ae7d8d1-1780-4cad-9200-9cfe90bb65fb
-- title:
--   Fixed-flattening loss from terrible coordinates
-- statement:
--   Let $\varphi$ be any Boolean ternary CSP, let $H$ be any finite set of birthday vertices on $\ell\le n$ coordinates per view, and let $r\ge0$. For every cross-consistent signed flattening $F=(A,B)$, with $t$ terrible coordinates,
--
--   $$|\Omega_F|\le\binom n\ell^{2r}\exp(-r(\ell/n)t).$$
--
--   Here $\Omega_F$ is the cell of accepted tuples sampled from $H$ with flattening $F$. This is the support-deficit part of fixed-cell counting. It requires neither a source-gap promise nor a bound on the cardinality of $H$; repetitions within each tuple side remain allowed.
-- source:
--   Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, proof of Lemma 4.5, equation (7), PDF p10 / printed p9; extends the same full-graph counting bound to arbitrary selected H and all repetition counts.

import Definitions.Def_BirthdayEntropy_Soundness_Biclique
noncomputable section
open scoped Classical
open BirthdayEntropy.Soundness

theorem BirthdayEntropy.Soundness.support_deficit_cell_bound {n m ℓ : ℕ} (φ : CSP n m) (H : Finset (Vertex n ℓ))
    (r : ℕ) (F : Flattening n) (hF : CrossConsistent F) (hℓn : ℓ ≤ n) :
    ((acceptedCell φ H r F).card : ℝ) ≤ (Nat.choose n ℓ : ℝ)^(2*r) *
      Real.exp (-(r : ℝ) * ratio n ℓ * (terrible F).card) := by sorry
