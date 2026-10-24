-- Prove2me | Theorems.Thm_ContextualAuctions_Existence_lemma_4_compact
-- name    : ContextualAuctions.Existence.lemma_4_compact
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T07:52:31.40288+00:00
-- url     : https://prove2.me/theorems/49cb479f-5dfa-4c0f-8d9f-5ba733a761bf
-- title:
--   Lemma 4 (1), p. 10 — $\mathcal X_0$ is compact in $L_1(\Theta)$
-- statement:
--   Work in the contextual first price auction model with budgets (see the `Setting` and `FixedPoint` modules), under its standing assumptions. Let
--   $$\mathcal X_0=\Big\{\mu\in L_1(\Theta)\ :\ \mu(w,B)\in\big[0,\omega/B_{\min}\big]\ \text{for }(w,B)\in\Theta,\ \ V(\mu,\Theta)\le V_0\Big\},$$
--   where $V(\mu,\Theta)=\sup\{\int_\Theta\mu\,\mathrm{div}\,\varphi:\varphi\in C^1_c(\Theta,\mathbb R^{d+1}),\ \|\varphi\|_\infty\le1\}$ is the total variation and $V_0=(d+1)\max(U^d,U^{d+1})\,\omega/B_{\min}$.
--
--   **Claim.** $\mathcal X_0$ is a compact subset of $L_1(\Theta)$ (Lebesgue measure on the box $\Theta$).
--
--   This is the compactness part of item 1 of Lemma 4 of the paper; it is the compactness of uniformly bounded sets of bounded-variation functions on a bounded box in $L_1$ (e.g. Ambrosio–Fusco–Pallara, Theorem 3.23), together with the closedness of the constraints under $L_1$ convergence (lower semicontinuity of the total variation). It supplies the compact domain needed for the Kakutani–Fan–Glicksberg fixed-point argument.
--
--   **Formalization Note** $\mathcal X_0$ is taken as the set `X0L M` of $L_1(\Theta)$ classes having a representative in `X0 M` (measurable pacing functions integrable on $\Theta$ with values in $[0,\omega/B_{\min}]$ on $\Theta$ and total variation at most $V_0$). The constant $V_0$ is the corrected one of the `FixedPoint` module.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science (2023), doi:10.1287/mnsc.2023.4719, p. 10, Lemma 4 item 1 (compactness of X_0 in L_1(Θ))

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting
import Definitions.Def_ContextualAuctions_Existence_FixedPoint

namespace ContextualAuctions.Existence

theorem lemma_4_compact (M : Model) (hM : M.Standing) : IsCompact (X0L M) := by sorry

end ContextualAuctions.Existence
