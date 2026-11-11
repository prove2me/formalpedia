-- Prove2me | Theorems.Thm_AgnHalfMem_claim_A_1
-- name    : AgnHalfMem.claim_A_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-10T09:12:52.375619+00:00
-- url     : https://prove2.me/theorems/6d2b1030-dfec-4b06-9b47-5fde9fd1f247
-- title:
--   Claim A.1 — the Gaussian sine integral $K(t)\ge0$, and $K(t)\ge 1/(2t)$ for $t\ge4$
-- statement:
--   Let $G\sim N(0,1)$ and $K(t)=\mathbb E[\sin(tG)\,\mathrm{sign}(G)]$. Then:
--
--   1. $K(t)=\mathbb E[\sin(t|G|)]$ for every $t\ge 0$;
--   2. $K(t)\ge 0$ for every $t\ge0$;
--   3. for every $t\ge 4$,
--   $$
--   K(t)\ \ge\ \frac1{2t}.
--   $$
--
--   This is the one-dimensional fact behind the correlation of sine functions with halfspaces: a sine of a Gaussian direction agrees with the sign of that direction with advantage of order $1/t$.
--
--   Differences from the source:
--   - encoding: K(t) = E_G[sin(tG)sign(G)] = E_G[sin(t|G|)] (definition with an identity) → Kfun t = E[sin(tG)·sgn(signB G)], the identity with E[sin(t|G|)] as the first conjunct; reason: the claim's display defines K by both expressions; the identity is stated, not assumed
-- source:
--   S. Garg, T. Jadhav, Memory-Sample Tradeoffs for Agnostically Learning Halfspaces, STOC 2027 submission (manuscript, PDF sha256 386bc9b3…43f84d5), Claim A.1, p.25

import Mathlib
import Definitions.Def_AgnHalfMem_Kfun

open MeasureTheory ProbabilityTheory

namespace AgnHalfMem

/-- **Claim A.1 (the Gaussian sine integral).** S. Garg, T. Jadhav, *Memory-Sample Tradeoffs for
Agnostically Learning Halfspaces*, STOC 2027 submission (manuscript, PDF sha256
386bc9b3…43f84d5), Claim A.1, p.25: "For G ∼ N(0, 1) and t ≥ 0, define
K(t) = E_G[sin(tG) sign(G)] = E_G[sin(t|G|)]. Then, 1. K(t) ≥ 0 for t ≥ 0. 2. K(t) ≥ 1/(2t) for
t ≥ 4."

**Formalization Note.** `Kfun t = E[sin(tG) sign(G)]`; the identity with `E[sin(t|G|)]` stated in
the claim is the first conjunct, the two numbered clauses are the second and third. -/
theorem claim_A_1 :
    (∀ t : ℝ, 0 ≤ t → Kfun t = ∫ g, Real.sin (t * |g|) ∂(gaussianReal 0 1)) ∧
    (∀ t : ℝ, 0 ≤ t → 0 ≤ Kfun t) ∧
    (∀ t : ℝ, 4 ≤ t → 1 / (2 * t) ≤ Kfun t) := by sorry

end AgnHalfMem
