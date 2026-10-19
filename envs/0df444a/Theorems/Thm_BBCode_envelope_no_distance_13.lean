-- Prove2me | Theorems.Thm_BBCode_envelope_no_distance_13
-- name    : BBCode.envelope_no_distance_13
-- status  : Open
-- author  : @Winningatmath
-- created : 2026-10-16T18:02:12.626986+00:00
-- url     : https://prove2.me/theorems/757e692d-3c0a-42a1-9b3e-9bfb7772409f
-- title:
--   §6 — no connected three-term weight-6 BB code with $n\le360$, $k\ge20$ has distance $\ge13$
-- statement:
--   Let $l,m\ge1$ with $n=2lm\le 360$, and let $A,B$ be polynomials in $\mathbb F_2[x,y]/(x^l-1,y^m-1)$ with exactly three terms each. Suppose the bivariate-bicycle code $\mathrm{BB}(A,B)$ has a connected Tanner graph and encodes $k\ge 20$ logical qubits. Then
--   $$\min(d_X,d_Z)\le 12,$$
--   that is, there is a nontrivial X-logical or a nontrivial Z-logical of weight at most $12$.
--
--   This is the negative half of the source's weight-6 envelope classification: no code in this family and size range reaches distance 13.
--
--   **Formalization Note** The statement ranges over all $l,m\ge1$ with $2lm\le360$ (971 shapes); the source's 961 omit the ten shapes with $lm\le5$, for which $k\ge20$ is impossible.
-- source:
--   B. W. Daugherty, S. Ryan, G. Ward, New distance-12 bivariate-bicycle codes with 20 and 24 logical qubits: an exhaustive classification and checkable distances to 360 qubits, Zenodo v1.0.0 (2026), https://doi.org/10.5281/zenodo.23382175, §6 (pp. 9–10) and Table 8

import Mathlib
import Definitions.Def_BBCode_Setting

namespace BBCode

theorem envelope_no_distance_13 (l m : ℕ) [NeZero l] [NeZero m] (hn : 2 * (l * m) ≤ 360)
    (A B : Poly l m) (hA : A.card = 3) (hB : B.card = 3) (hconn : IsConnected A B)
    (k : ℕ) (hk : NumLogical A B k) (hk20 : 20 ≤ k) :
    ∃ v, (IsXLogical A B v ∨ IsZLogical A B v) ∧ weight v ≤ 12 := by sorry

end BBCode
