-- Prove2me | Theorems.Thm_AdDataSharing_Base_lemma_1
-- name    : AdDataSharing.Base.lemma_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:47:00.486353+00:00
-- url     : https://prove2.me/theorems/c94259f4-ede2-42c8-8ac6-2695186942a2
-- title:
--   Lemma 1 — if ADX1 is closed, both advertisers contract with ADX1 in the unique equilibrium
-- statement:
--   Assume the standing assumptions $0<\alpha<\tfrac12$, $0<w<C<M<2C$, $0<\varphi<1$, $0<\eta_1<\eta_2$, and suppose $ADX_1$ does not allow cross-targeting. Then a profile of plans $\sigma=(\sigma_1,\sigma_2)$ is a subgame-perfect equilibrium of stages 2–3 if and only if
--   $$
--   \sigma_1 \text{ and } \sigma_2 \text{ both share data with } ADX_1 .
--   $$
--
--   When $ADX_1$ is closed, contracting with it only enlarges the look-alike audience an advertiser can reach, so it is a dominant choice. The lemma gives the continuation that $ADX_1$ compares against when deciding whether to open.
--
--   **Formalization Note.** Snipe decisions are irrelevant when $ADX_1$ is closed, so uniqueness is uniqueness of the exchange profile.
-- source:
--   Johnson, Jungbauer, Preuss, Online Advertising, Data Sharing, and Consumer Control, SSRN 3898798 (Nov. 2, 2022), p. 24, Lemma 1 (argument on p. 7, §1.1)

import Mathlib
import Definitions.Def_AdDataSharing_Base_Model

namespace AdDataSharing.Base

/-- Lemma 1 (p. 24): if ADX1 is closed, a profile is a subgame-perfect equilibrium of
stages 2–3 if and only if both advertisers contract with ADX1. -/
theorem lemma_1 (P : Params) (hP : P.Standing) (σ : Plan × Plan) :
    IsSPE P false σ ↔ σ.1.ex = .adx1 ∧ σ.2.ex = .adx1 := by sorry

end AdDataSharing.Base
