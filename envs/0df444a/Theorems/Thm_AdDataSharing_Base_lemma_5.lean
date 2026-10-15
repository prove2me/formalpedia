-- Prove2me | Theorems.Thm_AdDataSharing_Base_lemma_5
-- name    : AdDataSharing.Base.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:00.987525+00:00
-- url     : https://prove2.me/theorems/5e0906b9-ab64-40e6-84f6-32a365f06edc
-- title:
--   Lemma 5 — if ADX1 is open, there is always an equilibrium in pure strategies
-- statement:
--   Assume the standing assumptions $0<\alpha<\tfrac12$, $0<w<C<M<2C$, $0<\varphi<1$, $0<\eta_1<\eta_2$, and suppose $ADX_1$ allows cross-targeting. Then
--   $$
--   \exists\,\sigma\ \text{a subgame-perfect pure-strategy equilibrium of stages 2–3.}
--   $$
--
--   Existence matters for Proposition 1: when full cross-targeting is not an equilibrium, $ADX_1$ still needs some continuation to evaluate the open option.
--
--   **Formalization Note.** Pure strategies are the plans of the model (an exchange and a snipe decision per advertiser); the snipe decisions must be optimal on and off the path.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 25, Lemma 5 (proof pp. 26–27)

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- Lemma 5 (p. 25): if ADX1 is open, there is always a subgame-perfect equilibrium of
stages 2–3 in pure strategies. -/
theorem lemma_5 (P : Params) (hP : P.Standing) :
    ∃ σ : Plan × Plan, IsSPE P true σ := by sorry

end AdDataSharing.Base
