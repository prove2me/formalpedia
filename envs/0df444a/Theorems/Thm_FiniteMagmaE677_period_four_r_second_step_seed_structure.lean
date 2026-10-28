-- Prove2me | Theorems.Thm_FiniteMagmaE677_period_four_r_second_step_seed_structure
-- name    : FiniteMagmaE677.period_four_r_second_step_seed_structure
-- status  : Proved
-- author  : @shivm
-- created : 2026-10-26T02:05:33.307719+00:00
-- url     : https://prove2.me/theorems/980cfd5e-ee3b-40c9-83e0-b7298775881f
-- title:
--   R second-step seed: explicit fixer and own orbit of length at least six
-- statement:
--   Let a finite magma satisfy E677, and let four pairwise distinct points satisfy
--
--   $$x\diamond x=c_1,\quad x\diamond c_1=c_2,\quad x\diamond c_2=c_3,\quad x\diamond c_3=x.$$
--
--   Put $q=c_2\diamond x$ and $r=c_1\diamond c_2$. Assume the distinguished collision data
--
--   $$q=c_3\diamond x,\qquad c_1\diamond q=x,\qquad c_2\diamond q=c_1,$$
--
--   with $q\notin\{x,c_1,c_2,c_3\}$, and assume the R second-step relation $x\diamond q=r$.
--
--   Then
--
--   $$(q\diamond x)\diamond q=q,\qquad q\diamond q\ne q,\qquad
--   \operatorname{per}_{L_q}(q)\ge 6,$$
--
--   where $L_q(z)=q\diamond z$ and $\operatorname{per}_{L_q}(q)$ is its least positive return time at $q$. Thus the seed has an explicit fixer, is not idempotent, and its orbit under its own left multiplication contains at least six points.
--
--   This bounds the orbit under $L_q$, not the separately supplied first-return cycle of $q$ under $L_x$. It does not produce a fixer at $x$ or close D4.3b.
-- source:
--   Original auxiliary deduction for D4.3b, https://prove2.me/theorems/98f7dc30-3fa6-4160-89d8-62bd30c5e338, 2026-10-26. Uses the published D4Distinguished definition and E677 backward recurrence (Equational Theories Project, Chapter 13, Lemma 13.1(iii)); combines the established period-two and period-three exclusions with https://prove2.me/theorems/ff451fc6-7251-43c6-8df7-a46f0d30b451 and https://prove2.me/theorems/ef8ad662-742c-43ba-bae0-2e95204fac5d. The strengthened seed conclusion is derived in the accompanying proof.

import Definitions.Def_FiniteMagmaE677_d4_first_return

universe u

theorem FiniteMagmaE677.period_four_r_second_step_seed_structure {α : Type u} [Fintype α] (op : α → α → α)
    (h : FiniteMagmaE677.E677 op) (x c1 c2 c3 : α)
    (packet : FiniteMagmaE677.FirstReturn.D4Distinguished op x c1 c2 c3)
    (q_to_r : op x (op c2 x) = op c1 c2) :
    op (op (op c2 x) x) (op c2 x) = op c2 x ∧
    op (op c2 x) (op c2 x) ≠ op c2 x ∧
    6 ≤ Function.minimalPeriod (op (op c2 x)) (op c2 x) := by sorry
