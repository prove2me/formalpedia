-- Prove2me | Theorems.Thm_CNFLearnMQ_lemma_3_5
-- name    : CNFLearnMQ.lemma_3_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-09T23:12:41.778651+00:00
-- url     : https://prove2.me/theorems/74d27a48-810f-4154-84f6-f8f9447038c2
-- title:
--   Lemma 3.5 — $xG(1/x)$ is strictly decreasing on $(1,\infty)$
-- statement:
--   Let $G$ be the inverse of the binary entropy function $H$ restricted to $[0,1/2]$. The function
--   $$\varphi(x)=x\,G(1/x)$$
--   is strictly decreasing on $(1,\infty)$.
--
--   It is used in Lemma 5.12 to show that every strong extension decreases the normalized remaining width by more than $t\,G(1/t)$.
--
--   Differences from the source:
--   - encoding: $G$, the inverse of $H$ on $[0,1/2]$ → $G(y)=\inf\{x\in[0,1/2]: y\le H(x)\}$; reason: equal to the inverse for $y\in[0,1]$; the arguments $1/x$ with $x>1$ lie in $(0,1)$
-- source:
--   Feng, Yu, Zhang, Learning CNF Formulas with Uniform Random Solutions and Membership Queries, STOC 2027 submission (manuscript sha256 519ee6d4…), Lemma 3.5, p.15

import Mathlib
import Definitions.Def_CNFLearnMQ_Xi

set_option autoImplicit false

namespace CNFLearnMQ

/-- Lemma 3.5, p.15 (Feng, Yu, Zhang, *Learning CNF Formulas with Uniform Random Solutions and Membership Queries*, STOC 2027 submission (manuscript sha256 519ee6d4…)). The function `φ(x) = x·G(1/x)` is strictly decreasing on `(1, ∞)`,
where `G` is the inverse of the binary entropy function `H` restricted to `[0, 1/2]`. -/
theorem lemma_3_5 : StrictAntiOn (fun x : ℝ => x * G (1 / x)) (Set.Ioi 1) := by sorry

end CNFLearnMQ
