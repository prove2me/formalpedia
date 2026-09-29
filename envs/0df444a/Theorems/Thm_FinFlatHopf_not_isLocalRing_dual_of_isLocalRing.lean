-- Prove2me | Theorems.Thm_FinFlatHopf_not_isLocalRing_dual_of_isLocalRing
-- name    : FinFlatHopf.not_isLocalRing_dual_of_isLocalRing
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:43.415905+00:00
-- url     : https://prove2.me/theorems/c143e5ca-7484-5a09-aa66-bc924a9e8433
-- title:
--   Local Hopf algebra of rank n has non-local convolution dual
-- statement:
--   Let $B$ be a commutative ring which is a local ring, with maximal ideal $\mathfrak{m} =$ `IsLocalRing.maximalIdeal B`, and let $n$ be a natural number with $1 < n$ whose image in $B$ does not lie in $\mathfrak{m}^2$. Let $H$ be a commutative ring equipped with the structure of a Hopf algebra over $B$, free as a $B$-module, finite as a $B$-module, and of rank $\operatorname{finrank}_B H = n$, and assume that $H$ is itself a local ring. The assertion is that `WithConv (H →ₗ[B] B)`, the $B$-linear dual of $H$ equipped with the convolution product (the multiplication transposed from the comultiplication of $H$, with unit the counit), is not a local ring. So under the stated hypothesis on $n$ and the base, a commutative Hopf algebra of rank $n>1$ over $B$ cannot be local simultaneously with its convolution dual; no integrality, completeness or cocommutativity hypothesis on $B$ or $H$ is imposed, and nothing is assumed about the residue characteristic or about $n$ beyond $1<n$ and $n \notin \mathfrak{m}^2$.
--
--   This is the Hopf-algebra form of the statement that over an absolutely unramified base there is no finite flat group scheme of order $n$ that is connected with connected Cartier dual — in particular no lift of $\alpha_p$ — the relevant case of the Tate–Oort classification of group schemes of prime order. It feeds into [`FinFlatHopf.exists_subgroup_inertia_trivial_quotient_cyclotomic`](thm.html#FinFlatHopf.exists_subgroup_inertia_trivial_quotient_cyclotomic), and its proof invokes the left integral and Frobenius bijection of [`FinFlatHopf.exists_left_integral_frobenius`](thm.html#FinFlatHopf.exists_left_integral_frobenius).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_FinFlatHopf_not_isLocalRing_dual_of_isLocalRing.lean

import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Coalgebra.Convolution
import Mathlib.RingTheory.LocalRing.MaximalIdeal.Basic
import Mathlib.LinearAlgebra.Dimension.Finrank
import Mathlib.LinearAlgebra.FreeModule.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem FinFlatHopf.not_isLocalRing_dual_of_isLocalRing
    (B : Type) [CommRing B] [IsLocalRing B] (n : ℕ) (hn1 : 1 < n)
    (hn : (n : B) ∉ IsLocalRing.maximalIdeal B ^ 2)
    (H : Type) [CommRing H] [HopfAlgebra B H] [Module.Free B H] [Module.Finite B H]
    (hrank : Module.finrank B H = n) [IsLocalRing H] :
    ¬ IsLocalRing (WithConv (H →ₗ[B] B)) := by sorry
