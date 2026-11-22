-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002V2_lemma_4_3
-- name    : AehligSchwichtenberg2002V2.lemma_4_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T06:56:58.232983+00:00
-- url     : https://prove2.me/theorems/d07c5261-3d63-4a91-8a9e-9435217cf37f
-- title:
--   Lemma 4.3 — Terms of token type have a free variable
-- statement:
--   Every well-typed term of type $\diamond$ has a nonempty set of free variables. Its typing context is therefore nonempty.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg (2002), A syntactical analysis of non-size-increasing polynomial time computation, Lemma 4.3. https://arxiv.org/abs/cs/0011037

import Definitions.Def_AehligSchwichtenberg2002V2_Bounds

namespace AehligSchwichtenberg2002V2

theorem lemma_4_3 {Γ : Context} {t : Term}
    (ht : HasType Γ t .diamond) :
    Γ ≠ [] ∧ freeVars t ≠ [] := by sorry

end AehligSchwichtenberg2002V2
