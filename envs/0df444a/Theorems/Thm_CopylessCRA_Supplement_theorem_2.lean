-- Prove2me | Theorems.Thm_CopylessCRA_Supplement_theorem_2
-- name    : CopylessCRA.Supplement.theorem_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-17T02:58:39.86221+00:00
-- url     : https://prove2.me/theorems/be045201-9992-40bd-abc6-3b2febb5d833
-- title:
--   Theorem 2 (Two sectors) — unipotent and quasi-unipotent CCRA characterizations
-- statement:
--   Let $f:\Sigma^*\to\mathbb Q$ be a rational series, represented by an arbitrary minimal representation $(\lambda,M,\gamma)$ over a finite alphabet.
--
--   1. If every word matrix $M_w$ is unipotent, then the following are equivalent: $f$ is CCRA-computable; all minimal letter matrices commute; $f$ is invariant under permutations of input positions; and there is a rational polynomial $P$ such that
--      $$
--      f(w)=P((|w|_a)_{a\in\Sigma}).
--      $$
--   2. If every eigenvalue of every word matrix is a root of unity, then the following are equivalent: $f$ is CCRA-computable; any two unipotent word matrices commute; $\Gamma_f$ is virtually abelian; and there exist a finite group $F$, a morphism $\varphi:\Sigma^*\to F$, and polynomials $P_g\in\mathbb Q[n_{h,a}:h\in F,a\in\Sigma]$ such that
--      $$
--      f(w)=P_{\varphi(w)}((|w|_{h,a})_{h,a})
--      $$
--      for every word $w$, where $|w|_{h,a}$ uses the group state before reading the counted position.
--
--   This gives exact concrete forms for the two sectors of the main characterization.
--
--   Differences from the source:
--   - encoding: the source refers to the minimal representation intrinsically and describes unipotence, roots of unity and finite-group transition counts in prose → Lean takes an arbitrary supplied minimal representation, expresses unipotence as nilpotence of $M_w-I$, tests roots of its characteristic polynomials over $\overline{\mathbb Q}$ for quasi-unipotence, and bundles the finite group and word morphism; reason: minimal representations are unique up to conjugacy, nilpotence of $M_w-I$ is equivalent to every eigenvalue being $1$, characteristic-polynomial roots are exactly the eigenvalues with algebraic multiplicity, and the bundled data preserve the same instances
-- source:
--   Zeng–Cao–Dai–Wang–Ding, Copyless Cost Register Automata and Algebraic Groups, STOC 2027 submission (manuscript sha256 434d3094df2665371c402d5b5291b3c7f3a27a0d79384e4a8ec3ca3a46a92543), Theorem 2, p.3 (PDF p.5); proof p.13 (PDF p.15)

import Mathlib
import Definitions.Def_CopylessCRA_Supplement_IsUnipotentSeries

open Matrix

namespace CopylessCRA
namespace Supplement

/-- Zeng--Cao--Dai--Wang--Ding, *Copyless Cost Register Automata and Algebraic Groups*, STOC
2027 submission (manuscript sha256 434d3094...), Theorem 2 (Two sectors), p.3 (PDF p.5),
proved in Appendix A, p.13 (PDF p.15).

For a unipotent rational series, CCRA-computability, commutation of the minimal letter matrices,
permutation invariance, and a rational polynomial in the letter counts are equivalent.  For a
quasi-unipotent rational series, CCRA-computability, commutation of all unipotent word matrices,
virtual abelianness of the generated group, and the finite-group transition-count normal form are
equivalent.

**Formalization Note** `M` is an arbitrary supplied minimal representation of `f`, matching the
paper's intrinsic minimal representation up to conjugacy.  Both chains retain all four clauses.
The root-of-unity condition ranges over every word matrix.  In `transitionCount`, the group state
is measured before the current letter, and the chosen polynomial depends on the final state
`phi(w)`. -/
theorem theorem_2 {alpha iota : Type*} [Fintype alpha] [DecidableEq alpha]
    [Fintype iota] [DecidableEq iota] (f : List alpha -> ℚ) (lam : iota -> ℚ)
    (M : alpha -> Matrix iota iota ℚ) (gamma : iota -> ℚ)
    (hrep : IsRep f lam M gamma) (hmin : IsMinimalRep lam M gamma) :
    (IsUnipotentSeries M -> List.TFAE
      [C1 f,
       forall a b, Commute (M a) (M b),
       IsPermutationInvariant f,
       HasLetterCountPolynomial f]) ∧
    (IsQuasiUnipotentSeries M -> List.TFAE
      [C1 f,
       UnipotentWordMatricesCommute M,
       IsLetterGroupVirtuallyAbelian M,
       HasTransitionCountNormalForm f]) := by sorry

end Supplement
end CopylessCRA
