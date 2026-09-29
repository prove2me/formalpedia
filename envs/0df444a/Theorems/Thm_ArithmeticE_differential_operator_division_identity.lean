-- Prove2me | Theorems.Thm_ArithmeticE_differential_operator_division_identity
-- name    : ArithmeticE.differential_operator_division_identity
-- status  : Proved
-- author  : @shivm
-- created : 2026-09-11T16:02:58.946688+00:00
-- url     : https://prove2.me/theorems/26843522-aa89-42b5-81cc-8e25f2233d0d
-- title:
--   Explicit differential-operator transformation under division by one minus X
-- statement:
--   Let $D=d/dX$ be formal differentiation, let $g$ and $p_0,p_1,\ldots$ be complex formal power series, and let $n\ge0$. Then
--   $$\sum_{k=0}^n p_kD^k((1-X)g)=(1-X)\sum_{k=0}^n p_kD^kg-\sum_{k=0}^{n-1}(k+1)p_{k+1}D^kg.$$
--   This is the explicit transformation of a scalar differential operator under division by $1-X$. It applies in particular when the $p_k$ are polynomials, as in the classical E-function division argument. The underlying derivative identity is $D^{k+1}((1-X)g)=(1-X)D^{k+1}g-(k+1)D^kg$.
-- source:
--   Product differentiation in the classical E-function division argument: Beukers, https://webspace.science.uu.nl/~beuke106/siegelshidlovskii.pdf, proof of Corollary 2.2, pp. 3–4.

import Mathlib
open PowerSeries

theorem ArithmeticE.differential_operator_division_identity (p : ℕ → PowerSeries ℂ) (g : PowerSeries ℂ) (n : ℕ) :
    (∑ k ∈ Finset.range (n+1), p k * (PowerSeries.derivative ℂ)^[k] ((1-PowerSeries.X)*g)) =
      (1-PowerSeries.X)*(∑ k ∈ Finset.range (n+1), p k*(PowerSeries.derivative ℂ)^[k] g) -
      ∑ k ∈ Finset.range n, ((k+1:ℕ):PowerSeries ℂ)*p (k+1)*(PowerSeries.derivative ℂ)^[k] g := by sorry
