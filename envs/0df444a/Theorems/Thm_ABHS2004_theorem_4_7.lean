-- Prove2me | Theorems.Thm_ABHS2004_theorem_4_7
-- name    : ABHS2004.theorem_4_7
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:58:21.965386+00:00
-- url     : https://prove2.me/theorems/4d154f33-9db8-4048-8df3-fd719b97a5dc
-- title:
--   Theorem 4.7: Typing of Extracted Programs
-- statement:
--   For every natural deduction derivation `Δ; Γ ⊢ M : A` in `N-HA^ω` with `A` non-Harrop, the extracted program `⟦M⟧` is a well-typed term of the `!`-free affine term system of type `τ(A)` under the cleaned contexts `τ(Δ); τ(Γ)`.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Theorem 4.7, pp. 19-21.

import Definitions.Def_ABHS2004_Realizability

namespace ABHS2004

theorem theorem_4_7 {Δ Γ : ProofContext} {M : ProofTerm} {A : Formula}
    (hd : Derives Δ Γ M A)
    (hfresh : FreshRealizerVars Δ Γ M A) :
    WeaklyTyped (extractProof M) (tau A) ∧
    (∀ v ∈ freeVarOccurrences (extractProof M),
      v ∈ extractCtx Δ ∨ v ∈ extractCtx Γ) ∧
    HasType (extractCleaned M) (tauClean A) ∧
    (∀ v ∈ freeVarOccurrences (extractCleaned M),
      v ∈ extractCleanCtx Γ) := by sorry

end ABHS2004
