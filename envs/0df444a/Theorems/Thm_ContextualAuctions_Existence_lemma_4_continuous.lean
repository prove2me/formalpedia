-- Prove2me | Theorems.Thm_ContextualAuctions_Existence_lemma_4_continuous
-- name    : ContextualAuctions.Existence.lemma_4_continuous
-- status  : Proved
-- author  : @tianyipeng
-- created : 2026-10-23T07:52:16.542432+00:00
-- url     : https://prove2.me/theorems/615ba9b1-a0b4-4294-a9db-ca097470bc9f
-- title:
--   Lemma 4 (2), p. 10 — $f:\mathcal X_0\times\mathcal X_0\to\mathbb R$ is continuous
-- statement:
--   Work in the contextual first price auction model with budgets (see the `Setting` and `FixedPoint` modules), under its standing assumptions. For pacing functions $\mu,\hat\mu$ let
--   $$f(\mu,\hat\mu)=\mathbb E_{(w,B)\sim G}\big[q^\mu\big(w,B,\hat\mu(w,B)\big)\big],$$
--   where $q^\mu(w,B,t)=\sup_{b}\mathbb E\big[(w^T\alpha-(1+t)b(\alpha))\mathbf 1\{b(\alpha)\ge\max(r(\alpha),\{\beta^\mu(\theta_i,\alpha)\}_i)\}\big]+tB$ is the dual function, and let $\mathcal X_0\subset L_1(\Theta)$ be the set of pacing functions with values in $[0,\omega/B_{\min}]$ and total variation at most $V_0$.
--
--   **Claim.** $f:\mathcal X_0\times\mathcal X_0\to\mathbb R$ is continuous when $\mathcal X_0\times\mathcal X_0$ carries the product of the $L_1(\Theta)$ topologies.
--
--   This is item 2 of Lemma 4 of the paper, one of the hypotheses of the Kakutani–Fan–Glicksberg argument for Proposition 2.
--
--   **Formalization Note** $\mathcal X_0$ is the set `X0L M` of $L_1(\Theta)$ classes with a representative in `X0 M`, and $f$ is evaluated on the canonical representatives of the classes (`fL M`); on `X0L M` this does not depend on the choice of representative.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science (2023), doi:10.1287/mnsc.2023.4719, p. 10, Lemma 4 item 2

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint

namespace ContextualAuctions.Existence

theorem lemma_4_continuous (M : Model) (hM : M.Standing) :
    ContinuousOn (fun p : L1Theta M × L1Theta M => fL M p.1 p.2) (X0L M ×ˢ X0L M) := by sorry

end ContextualAuctions.Existence
