-- Prove2me | Theorems.Thm_CodeSW_lemma_29
-- name    : CodeSW.lemma_29
-- status  : Open
-- author  : @iris
-- created : 2026-11-07T02:28:45.8391+00:00
-- url     : https://prove2.me/theorems/93763b34-59fc-4187-83f9-9fa18bd6a239
-- title:
--   Lemma 29 [Ull14] — $P_{\mathrm{SW}}=M(\prod_e T_e)M^*$ and $P_{\mathrm{SC}}=\frac I2+\frac1{2|E|}M(\sum_e T_e)M^*$
-- statement:
--   Let $0<p<1$ and let $M,M^*,T_e$ be the operators of Appendix A. Then
--
--   1. $P_{\mathrm{SW}}=M\bigl(\prod_{e\in E}T_e\bigr)M^*$;
--   2. $P_{\mathrm{SC}}=\frac I2+\frac1{2|E|}M\bigl(\sum_{e\in E}T_e\bigr)M^*$.
--
--   The first identity expresses a full Swendsen-Wang step as resampling every check, and the second expresses a single-check step as resampling one random check. Together they reduce the comparison of the two chains to operator inequalities.
--
--   Differences from the source:
--   - encoding: ∏_{e∈E} T_e, with no order given → the matrix product in the order e = 0, 1, …, c − 1; reason: the T_e commute by Lemma 28 (iii), so the order does not matter
--   - encoding: 1/(2|E|) with |E| = c → Lean's 1/0 = 0 at c = 0, where both sides of (ii) are I/2; reason: the page has no case c = 0; this changes no instance with c ≥ 1
-- source:
--   Hangleiter, Ju, Vazirani, Code Swendsen-Wang Dynamics, arXiv:2510.08446 (manuscript sha256 4e4abb5e…), Lemma 29, p.35

import Definitions.Def_CodeSW_fk
import Definitions.Def_CodeSW_metropolis
open Matrix

namespace CodeSW

/-- **Lemma 29 [Ull14].** With the FK operators `T_e`, `M`, `M*`:
1. `P_SW = M (∏_{e∈E} T_e) M*`;
2. `P_SC = I/2 + (1/(2|E|)) M (∑_{e∈E} T_e) M*`
(Hangleiter, Ju, Vazirani, *Code Swendsen-Wang Dynamics*, arXiv:2510.08446, manuscript sha256
4e4abb5e…, Lemma 29, p.35).

**Formalization Note** The product is taken in the order `e = 0, 1, …, c − 1`
(`List.finRange c`); the `T_e` commute (Lemma 28 (iii)), so the order is immaterial. `|E| = c`. With
no checks (`c = 0`) the page's `1/(2|E|)` is undefined; Lean's `1/0 = 0` makes both sides of (ii)
`I/2`, a junk row that no later statement uses. -/
theorem lemma_29 {c n : ℕ} (h : Matrix (Fin c) (Fin n) (ZMod 2)) (p : ℝ) (hp0 : 0 < p)
    (hp1 : p < 1) :
    swRC h p = liftM h * ((List.finRange c).map (resample h p)).prod * liftMStar ∧
    singleCheck h p = (1 / 2 : ℝ) • (1 : Matrix (Finset (Fin c)) (Finset (Fin c)) ℝ) +
      (1 / (2 * (c : ℝ))) • (liftM h * (∑ e : Fin c, resample h p e) * liftMStar) := by sorry

end CodeSW
