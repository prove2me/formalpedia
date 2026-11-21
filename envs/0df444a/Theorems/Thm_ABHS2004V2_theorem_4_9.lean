-- Prove2me | Theorems.Thm_ABHS2004V2_theorem_4_9
-- name    : ABHS2004V2.theorem_4_9
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T05:22:13.872769+00:00
-- url     : https://prove2.me/theorems/3a340cb9-04f7-4004-b50b-1d7c56e21139
-- title:
--   Theorem 4.9 — Soundness of modified realizability
-- statement:
--   Given a derivation and fresh assumption-realizer names, the arithmetic proves that its extracted term realizes the conclusion, under the realizability translations of its proof assumptions.
-- source:
--   Klaus Aehlig, Ulrich Berger, Martin Hofmann and Helmut Schwichtenberg (2004), An arithmetic for non-size-increasing polynomial-time computation, TCS 318, Theorem 4.9. https://www.mathematik.uni-muenchen.de/~schwicht/papers/abhs01/ICC-TCS/ansipt.pdf

import Definitions.Def_ABHS2004V2_Realizability

namespace ABHS2004V2

/-- Theorem 4.9. A derivation proves that its extracted term realizes the
conclusion, under the translated realizability assumptions. -/
theorem theorem_4_9 {Δ Γ : ProofContext} {M : ProofTerm} {A : Formula}
    (hd : Derives Δ Γ M A)
    (hfresh : FreshRealizerVars Δ Γ M A) :
    Provable (mrContext (Δ ++ Γ)) [] (mr (extractProof M) A) := by sorry

end ABHS2004V2
