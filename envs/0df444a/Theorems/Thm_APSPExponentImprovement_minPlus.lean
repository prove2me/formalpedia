-- Prove2me | Theorems.Thm_APSPExponentImprovement_minPlus
-- name    : APSPExponentImprovement.minPlus
-- status  : Proved
-- author  : @wurtle
-- created : 2026-10-06T14:16:07.552782+00:00
-- url     : https://prove2.me/theorems/6b8f9398-4139-4a3c-af9e-b12f3d20e10f
-- title:
--   Min-plus product in $O(n^r)$ for every $r>2.99825$
-- statement:
--   For every rational $r>2.99825$, compute the exact min-plus product of two $n\times n$ integer matrices in $O(n^r)$ steps. Each output entry is an attained minimum $C_{ij}=\min_{k<n}(A_{ik}+B_{kj})$, written row by row. For every fixed natural weight exponent $\kappa$, there must be a single finite deterministic word-RAM program, a word-width constant $b$, and a time bound $T$ working for all sizes $n$ and all word widths $W\ge b(\operatorname{Nat.log2}(n)+1)$. Every encoded input integer has absolute value at most $n^\kappa$. Correctness includes $n=0,1$; the asymptotic bound is required for $n\ge2$. The machine must accept and write the required exact output. The program and constants may depend on r as well as the weight exponent. For n=0 there are no output entries. This is an unconditional algorithm-existence statement; the all-edges theorem is a proposed proof route, not an assumption of the goal.
-- source:
--   https://arxiv.org/html/2610.06783v1#S6; Theorems 17 and 19, conclusion footnote 10; https://people.csail.mit.edu/rrw/finding-full.pdf; https://theory.stanford.edu/~virgi/tria-mmult-jv.pdf

import Definitions.Def_TrulySubcubicAPSP_Problems

set_option autoImplicit false
set_option relaxedAutoImplicit false

theorem APSPExponentImprovement.minPlus :
    ∀ r : Rat, 2.99825 < r →
      TrulySubcubicAPSP.MinPlusProduct.SolvedInTime r := by sorry
