-- Prove2me | Theorems.Thm_AlpoGe_cyclic_character_logDeriv_locally_bounded_below_record_of_row
-- name    : AlpoGe.cyclic_character_logDeriv_locally_bounded_below_record_of_row
-- status  : Open
-- author  : @RSoulat
-- created : 2026-11-22T17:27:27.839078+00:00
-- url     : https://prove2.me/theorems/3eb65d38-ff09-4446-80bd-dc26c1d8b0c0
-- title:
--   Local boundedness of the logarithmic derivative for the cyclic character product
-- statement:
--   Assume the local–global compatibility statement `Row0b` with reciprocity laws `IsRecT`. Let $\chi$ be a primitive complex Dirichlet character of positive modulus $N$, and let $X=\langle\chi\rangle$ in the finite group of Dirichlet characters modulo $N$. Let
--   $$
--   F_\chi(w)=\prod_{\eta\in X}L(\eta,w),
--   $$
--   where each factor uses its modulus-$N$ Dirichlet $L$-function. For every $s$ with $1/2<\Re s\leq 0.8749570698$, show that there are a real constant $C$ and a punctured neighborhood of $s$ on which $|F_\chi'(w)/F_\chi(w)|\leq C$.
--
--   This is a local analytic sufficient condition for the primitive nonvanishing reduction. The cyclic grouping is the one used to define the levels in Alpöge's zero-free argument, expressed using the characters at their common modulus.
-- source:
--   Reduction of https://prove2.me/theorems/fed98188-9fd8-4c13-b49d-5f90b48e16ba using local pole detection and the cyclic grouping in L. Alpöge, https://github.com/leanprover-community/riemann-hypothesis/blob/8f328277481a6178eb0dbbb262b2419a3c8bfe02/src/Development/AutomorphicArithmetic/CharacterBoxes/ZeroFreeAllOfTopG.lean#L30-L38.

import Definitions.Def_AlpoGeB008
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Analysis.Meromorphic.Order

open Filter
open scoped Topology Classical
set_option autoImplicit false

namespace AlpoGe

theorem cyclic_character_logDeriv_locally_bounded_below_record_of_row
    (H : UpperTheory.GalStar.Row0b fun h rc => UpperTheory.Zero.LLC.IsRecT h rc) :
    ∀ (N : ℕ) [NeZero N] (χ : DirichletCharacter ℂ N), χ.IsPrimitive →
      ∀ s : ℂ, 1 / 2 < s.re → s.re ≤ (0.8749570698 : ℝ) →
        ∃ C : ℝ, ∀ᶠ z in 𝓝[≠] s,
          ‖logDeriv (fun w => ∏ η ∈ Finset.univ.filter (· ∈ Subgroup.zpowers χ),
            DirichletCharacter.LFunction η w) z‖ ≤ C := by sorry

end AlpoGe
