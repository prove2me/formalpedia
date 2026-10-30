-- Prove2me | Theorems.Thm_ABHS2004_theorem_4_9
-- name    : ABHS2004.theorem_4_9
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:58:45.816332+00:00
-- url     : https://prove2.me/theorems/8153f9a2-f87b-4253-b9ba-b757d52d00d7
-- title:
--   Theorem 4.9: Soundness of Modified Realizability for N-HA^ω
-- statement:
--   If `Δ; Γ ⊢ M : A` is a derivation in `N-HA^ω` and all assumptions in `Δ, Γ` are realized in environment `η`, then the value `⟦⟦M⟧⟧_η` (or `ε` if `A` is Harrop) realizes `A` (`r mr A`).
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann, and Helmut Schwichtenberg, 'An arithmetic for non-size-increasing polynomial-time computation', Theoretical Computer Science 318(1-2), 2004, pp. 3-27 (doi:10.1016/j.tcs.2003.10.023). Theorem 4.9, pp. 22-23.

import Definitions.Def_ABHS2004_Realizability

namespace ABHS2004

theorem theorem_4_9 {Δ Γ : ProofContext} {M : ProofTerm} {A : Formula}
    (hd : Derives Δ Γ M A)
    (hfresh : FreshRealizerVars Δ Γ M A) :
    Provable (mrContext (Δ ++ Γ)) [] (mr (extractProof M) A) := by sorry

end ABHS2004
