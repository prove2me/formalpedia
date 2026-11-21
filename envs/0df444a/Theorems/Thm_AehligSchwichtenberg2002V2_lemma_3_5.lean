-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002V2_lemma_3_5
-- name    : AehligSchwichtenberg2002V2.lemma_3_5
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T20:43:05.748026+00:00
-- url     : https://prove2.me/theorems/481ffeb1-53d7-419c-9af0-32160f7b89ad
-- title:
--   Lemma 3.5 — Subject reduction
-- statement:
--   If $\Gamma$ types $t$ at $\tau$ and $t$ reduces to $t^\prime$ in one step, then the same context types $t^\prime$ at $\tau$.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg (2002), A syntactical analysis of non-size-increasing polynomial time computation, Lemma 3.5. https://arxiv.org/abs/cs/0011037

import Definitions.Def_AehligSchwichtenberg2002V2_Syntax

namespace AehligSchwichtenberg2002V2

theorem lemma_3_5 {Γ : Context} {t t' : Term} {τ : Ty}
    (ht : HasType Γ t τ) (hred : RedStep t t') :
    HasType Γ t' τ := by sorry

end AehligSchwichtenberg2002V2
