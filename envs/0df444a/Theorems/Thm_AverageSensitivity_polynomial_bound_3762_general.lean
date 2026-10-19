-- Prove2me | Theorems.Thm_AverageSensitivity_polynomial_bound_3762_general
-- name    : AverageSensitivity.polynomial_bound_3762_general
-- status  : Proved
-- author  : @Yuxuan Xu
-- created : 2026-10-16T12:51:39.676715+00:00
-- url     : https://prove2.me/theorems/e1a9c1cb-97c1-4ea0-a4ad-d43e8412ac61
-- title:
--   Average sensitivity of polynomial threshold functions is at most 3.762 d sqrt(n)
-- statement:
--   For all positive integers n,d, let p be any real polynomial in n variables with total degree at most d. On the uniform cube {-1,1}^n, define f(x)=1 when p(x)>=0 and f(x)=-1 otherwise. Let average sensitivity be the sum over coordinates of the probability that flipping that coordinate changes f. Then
--   $$\operatorname{AS}(f)\le\frac{1881}{500}d\sqrt n.$$
--   The theorem includes zeros of p under the positive-at-zero convention and arbitrary polynomials, with no multilinearity assumption. There is no restriction d<=n. The weighted-grading construction is due to OpenAI; the refined coupling estimate is due to Lagdive, Aglave and Damre. This result formalizes their integration and extracts the sufficient coefficient 3.762; optimality is not asserted.
-- source:
--   https://github.com/Anchen0823/average-sensitivity-lean/blob/b2e634415548e050c115f6f12732d8b6b4a5d27f/AverageSensitivity/Multilinearization.lean

import Mathlib
import Definitions.Def_GotsmanLinial
open OAI.LeanBlast.GotsmanLinial
open scoped BigOperators

theorem AverageSensitivity.polynomial_bound_3762_general {n d : ℕ} (hn : 1≤n) (hd : 1≤d)
    (p : MvPolynomial (Fin n) ℝ) (hdegree : p.totalDegree≤d) :
    averageSensitivity (polynomialThreshold p) ≤ (1881/500:ℝ)*(d:ℝ)*Real.sqrt (n:ℝ) := by sorry
