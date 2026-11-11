-- Prove2me | Theorems.Thm_ExactDFTRefine_Main_eq_12
-- name    : ExactDFTRefine.Main.eq_12
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-11T04:02:02.617814+00:00
-- url     : https://prove2.me/theorems/1f0df8a5-1584-4bba-90c8-6f0ac84c61fd
-- title:
--   §4, Eq. (12) — moments multiply under tensor powers: M_t(A^{⊗v}) = M_t(A)^v
-- statement:
--   For a finite multiset $A$, the tensor product $A \otimes B$ contains every product $ab$, with multiplicity, for $a \in A$, $b \in B$, and $A^{\otimes v}$ is the $v$-fold tensor power. For every real $t$,
--   $$M_t(A^{\otimes v}) = M_t(A)^v.$$
--   This is what lets Lemma 4.1 express the moments of the $v$-fold tensor unit through $P_t$, $P_1$ and $|T|$.
--
--   Differences from the source:
--   - generalization: finite multisets of positive integers and the v-fold tensor power, v ≥ 1 → every A : Multiset ℕ (zero entries allowed) and every v : ℕ, with A^{⊗0} = {1}; reason: the identity holds verbatim for nonnegative ranks and for v = 0 (both sides equal 1); the paper's case is the instance with positive entries and v ≥ 1
-- source:
--   Yao, Liu, A Numerical Refinement of an Exact Discrete Fourier Transform Bound, arXiv:2611.01257v1, p. 5, §4, Eq. (12)

import Mathlib
import Definitions.Def_ExactDFTRefine_Main_Moments

namespace ExactDFTRefine.Main

/-- **§4, Eq. (12)**, p. 5. Moments multiply under tensor powers: `M_t(A^{⊗v}) = M_t(A)^v`. -/
theorem eq_12 (t : ℝ) (A : Multiset ℕ) (v : ℕ) :
    moment t (tpow A v) = moment t A ^ v := by sorry

end ExactDFTRefine.Main
