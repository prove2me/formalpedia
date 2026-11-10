-- Prove2me | Theorems.Thm_BirthdayEntropy_Soundness_role_set_encoding
-- name    : BirthdayEntropy.Soundness.role_set_encoding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T07:50:01.787969+00:00
-- url     : https://prove2.me/theorems/cf788c03-efcb-4a2b-8860-a3fc68106d17
-- title:
--   Lemma 4.6 — Role-set encoding inequality
-- statement:
--   There exists an absolute $C>0$, uniform in every variable below, such that for every real $0<x\le1/2$, with $A_0=\log(e/x)$, and integers $0\le b\le m\le n$,
--   $$\log\binom mb\le CA_0\big((m-b)+xb\big).$$
--   The cases $b=0$ and $b=m$ are included. Both summands are inside the factor $CA_0$. This inequality bounds the information needed to specify a moving bad-role set.
--
--   Differences from the source:
--   - generalization: x=ell/n in the standing small-ratio range → any real 0<x<=1/2 independently of n,m,b; reason: the source proof uses only this range of x; every admitted ell/n is covered
--   - encoding: nonnegative integer indices and m-b → natural indices with b<=m and real subtraction after casting; reason: the difference equals the source integer difference under the stated ordering
-- source:
--   Alexandru Popa, Entropy-Weighted Soundness for Multi-Answer Birthday Graphs, STOC 2027 submission #907 (October 2026), https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/907.pdf, Lemma 4.6, PDF pp12 / printed pp11

import Mathlib
import Definitions.Def_BirthdayEntropy_Soundness_Source

noncomputable section
open scoped Classical

namespace BirthdayEntropy.Soundness

/-- Lemma 4.6 (12), PDF p12 / printed p11. C is uniform in x as well
as in b,m,n. Both b=0 and b=m are included. -/
theorem role_set_encoding :
    ∃ C : ℝ, 0 < C ∧ ∀ (x : ℝ), 0 < x → x ≤ 1/2 →
      ∀ (n m b : ℕ), b ≤ m → m ≤ n →
        Real.log (Nat.choose m b : ℝ) ≤
          C * Real.log (Real.exp 1 / x) * (((m : ℝ) - b) + x * b) := by sorry

end BirthdayEntropy.Soundness
