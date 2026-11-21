-- Prove2me | Theorems.Thm_ABHS2004V2_theorem_4_7
-- name    : ABHS2004V2.theorem_4_7
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T05:21:42.948753+00:00
-- url     : https://prove2.me/theorems/284b9079-4d70-48cd-b4a0-1ed2d27244d7
-- title:
--   Theorem 4.7 — Typing soundness of program extraction
-- statement:
--   With the paper’s convention for fresh assumption names, extraction gives a weakly typed term of the realizer type whose free variables come from the two proof contexts. The cleaned term is affinely typed at the cleaned realizer type and uses only realizers from the active context.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann and Helmut Schwichtenberg (2004), An arithmetic for non-size-increasing polynomial-time computation, TCS 318, Theorem 4.7. https://www.mathematik.uni-muenchen.de/~schwicht/papers/abhs01/ICC-TCS/ansipt.pdf

import Definitions.Def_ABHS2004V2_Realizability

namespace ABHS2004V2

/-- Theorem 4.7. The extracted term is weakly typed and refers only to realizers
of the proof assumptions. The cleaned extracted term is affinely typed and its
free variables come from the active context. -/
theorem theorem_4_7 {Δ Γ : ProofContext} {M : ProofTerm} {A : Formula}
    (hd : Derives Δ Γ M A)
    (hfresh : FreshRealizerVars Δ Γ M A) :
    WeaklyTyped (extractProof M) (tau A) ∧
    (∀ v ∈ freeVarOccurrences (extractProof M),
      v ∈ extractCtx Δ ∨ v ∈ extractCtx Γ) ∧
    HasType (extractCleaned M) (tauClean A) ∧
    (∀ v ∈ freeVarOccurrences (extractCleaned M),
      v ∈ extractCleanCtx Γ) := by sorry

end ABHS2004V2
