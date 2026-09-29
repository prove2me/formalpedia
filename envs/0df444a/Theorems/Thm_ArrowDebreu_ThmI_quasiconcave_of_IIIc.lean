-- Prove2me | Theorems.Thm_ArrowDebreu_ThmI_quasiconcave_of_IIIc
-- name    : ArrowDebreu.ThmI.quasiconcave_of_IIIc
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T17:38:07.961484+00:00
-- url     : https://prove2.me/theorems/83aadc3d-63d8-4591-87c6-6b0aed2dddf8
-- title:
--   III.c with continuity implies quasi-concave utility (§1.3.1)
-- statement:
--   Let an economy satisfy Assumption II (each consumption set $X_i$ is closed, convex and bounded below), Assumption III.a ($u_i$ is continuous on $X_i$) and Assumption III.c (if $u_i(x_i) > u_i(x_i')$ and $0<t<1$ then $u_i[t x_i + (1-t)x_i'] > u_i(x_i')$). Then every $u_i$ is **quasi-concave** on $X_i$: for every real $\alpha$ the upper level set
--   $$\{x_i \in X_i : u_i(x_i) \ge \alpha\}$$
--   is convex.
--
--   This is the form in which III.c enters the equilibrium-existence lemma, which asks for pay-offs quasi-concave in the player's own action.
--
--   **Formalization Note** The paper says quasi-concavity "is indeed implied by III.c."; its argument also uses III.a and the convexity of $X_i$, both of which are hypotheses here. III.c alone does not suffice: on $\mathbb R$, the function equal to $-1$ at one point and $0$ elsewhere satisfies III.c but is not quasi-concave.
-- source:
--   Arrow & Debreu, Existence of an Equilibrium for a Competitive Economy, Econometrica 22 (1954), https://doi.org/10.2307/1907353, p. 269 (PDF p. 6), §1.3.1, small-print paragraph after III.c

import Mathlib
import Definitions.Def_ArrowDebreu_Shared_Economy
import Definitions.Def_ArrowDebreu_ThmI_AssumptionsItoIV
open ArrowDebreu.Shared

namespace ArrowDebreu.ThmI

/-- **§1.3.1 (small print)**, Arrow & Debreu, Econometrica 22 (1954), p. 269 (PDF p. 6): the
quasi-concavity of `u_i` — the set `{x_i | x_i ∈ X_i and u_i(x_i) ≧ α}` is convex for every real
`α` — "is indeed implied by III.c. (but is obviously weaker)".

**Formalization Note.** The paper's proof uses III.a ("Then, from III.a., we can find x⁴ …") and
the convexity of `X_i` (Assumption II), so both are hypotheses: III.c alone does not imply
quasi-concavity (on `ℝ`, `u = −1` at one point and `0` elsewhere satisfies III.c). Mathlib's
`QuasiconcaveOn ℝ s f` says exactly that every upper level set `{x ∈ s | r ≤ f x}` is convex. -/
theorem quasiconcave_of_IIIc {l m n : ℕ} (E : Economy l m n) (hII : AssumptionII E)
    (hIIIa : AssumptionIIIa E) (hIIIc : AssumptionIIIc E) :
    ∀ i, QuasiconcaveOn ℝ (E.X i) (E.u i) := by sorry

end ArrowDebreu.ThmI
