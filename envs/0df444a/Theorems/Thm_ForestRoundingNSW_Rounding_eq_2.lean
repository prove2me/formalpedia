-- Prove2me | Theorems.Thm_ForestRoundingNSW_Rounding_eq_2
-- name    : ForestRoundingNSW.Rounding.eq_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T02:50:25.767572+00:00
-- url     : https://prove2.me/theorems/21be1638-f0ac-4f68-8bb9-f439a7ddc4a4
-- title:
--   §2.2, Eq. (2) — F is affine in each coordinate and ∂_j F(z) = E[f(R_{−j}(z) ∪ {j}) − f(R_{−j}(z))]
-- statement:
--   Let $X$ be a finite set, $f:2^X\to\mathbb R$ a set function with multilinear extension $F$, and $z\in[0,1]^X$. Then $F$ is affine in each coordinate: for every $j$ there are constants $a,c$ with $F(z_{-j},t)=a+ct$ for all $t\in[0,1]$, where $(z_{-j},t)$ is $z$ with its $j$-th coordinate replaced by $t$. Moreover, for every $j\in X$,
--   $$\partial_jF(z)=\mathbb E\big[f(R_{-j}(z)\cup\{j\})-f(R_{-j}(z))\big],$$
--   where $R_{-j}(z)$ contains each $h\in X\setminus\{j\}$ independently with probability $z_h$.
--
--   This is the basic calculus of the multilinear extension used by every rounding step: a partial derivative is an expected marginal value.
--
--   Differences from the source:
--   - generalization: a normalized set function f : 2^M → ℝ≥0 → any f : Finset X → ℝ; reason: the identity is algebraic and uses neither normalization nor nonnegativity; the source's f is a special case
--   - encoding: the ground set M → a finite type X with decidable equality; reason: Lean convention; same instances
--   - encoding: ∂_j F(z) → the derivative at t = 0 of t ↦ F(z + t e_j) for the polynomial F of Eq. (1); reason: this is the partial derivative of the polynomial F
--   - encoding: the expectation over R_{−j}(z) → the explicit sum over S ⊆ X \ {j} weighted by ∏_{h∈S} z_h ∏_{h∈X∖{j}∖S} (1 − z_h); reason: this is the law of independent sampling
--   - reading: F is affine in each coordinate → for every z ∈ [0,1]^X and j, t ↦ F(z with z_j := t) agrees with an affine function on [0,1]; reason: F is defined on [0,1]^M in the source
-- source:
--   Feng, Hu, Li, Zhang, Correlated Forest Rounding for Unweighted Nash Social Welfare, STOC 2027 submission (manuscript sha256 0c7af642…), p. 14, §2.2, Eq. (2)

import Mathlib
import Definitions.Def_NonmonotoneSubmod_Shared_F
import Definitions.Def_ForestRoundingNSW_Rounding_SetFunctions

open NonmonotoneSubmod.Shared

namespace ForestRoundingNSW.Rounding

theorem eq_2 {X : Type} [Fintype X] [DecidableEq X] (f : Finset X → ℝ) (z : X → ℝ)
    (hz : InUnitCube z) :
    (∀ j : X, ∃ a c : ℝ, ∀ t ∈ Set.Icc (0 : ℝ) 1, F f (Function.update z j t) = a + c * t) ∧
    ∀ j : X, partialDeriv (F f) j z =
      sampleExp z (Finset.univ.erase j) (fun S => f (insert j S) - f S) := by sorry

end ForestRoundingNSW.Rounding
