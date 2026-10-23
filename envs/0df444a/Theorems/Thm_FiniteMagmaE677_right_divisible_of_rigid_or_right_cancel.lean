-- Prove2me | Theorems.Thm_FiniteMagmaE677_right_divisible_of_rigid_or_right_cancel
-- name    : FiniteMagmaE677.right_divisible_of_rigid_or_right_cancel
-- status  : Proved
-- author  : @mysticflounder
-- created : 2026-10-23T01:11:51.70437+00:00
-- url     : https://prove2.me/theorems/946de1bc-98b3-41fb-ba0c-c3235be4e134
-- title:
--   Counterexample structure (o) — Condition (R) of (n) holds for rigid fibres with E255 and for finite right-cancellative fibres
-- statement:
--   Let $\diamond_E$ be an operation on a set $E$. Call a quadruple $(\alpha,a,b,c)$ of automorphisms of $(E,\diamond_E)$ a solution when
--
--   $$s=t\diamond_E\bigl(\alpha(s)\diamond_E((a(t)\diamond_E b(s))\diamond_E c(t))\bigr)\quad\text{for all } s,t\in E.$$
--
--   (For $\alpha=a=b=c=\mathrm{id}$ this is E677 for $\diamond_E$.) $E$ is rigid when the only solution is $(\mathrm{id},\mathrm{id},\mathrm{id},\mathrm{id})$, and right-cancellative when $a\diamond_E b=a'\diamond_E b$ gives $a=a'$. Condition (R) of Counterexample structure (n) says: for every solution $(\alpha,a,b,c)$ and every $s\in E$, some $r\in E$ satisfies $r\diamond_E b(s)=a(s)$.
--
--   **Theorem.** (R) holds in each of these two cases:
--
--   1. $E$ is rigid and satisfies E255;
--   2. $E$ is finite and right-cancellative.
--
--   **Proof idea.** In case 1, rigidity gives $a=b=\mathrm{id}$, and $r=(s\diamond_E s)\diamond_E s$ satisfies $r\diamond_E s=s$ by E255. In case 2, the map $r\mapsto r\diamond_E b(s)$ is injective on the finite set $E$, so it is onto.
--
--   **With (n).** If $Q\times E$ satisfies hypotheses 1–3 of Counterexample structure (n), and $E$ is finite and either rigid with E255 or right-cancellative, then $Q\times E$ satisfies E255. The two Lean statements compose with no other step. For a right-cancellative fibre, Counterexample structure (p) allows any permutations as twists.
--
--   **Use in a counterexample search.** A minimum counterexample of the form in (n) needs a fibre that fails (R), so a fibre that is neither rigid with E255 nor right-cancellative. Our computer check of the E677 tables in the ICARM database (not a proof and not part of this theorem): of the 1297 tables of order at most 100, 59 are not right-cancellative, and each of these 59 is rigid. Above order 100, among the tables that are not right-cancellative, 101 are not rigid (3 were not tested), and (R) holds in each of the 101.
--
--   **Prior work.** The twisted construction is B. Le Floch's (ETP Zulip thread "FINITE: 677 -> 255", 2024-12-18); see (n). The two cases are short arguments. Condition (R) and its use in (n) were not found in the ETP blueprint, the ETP paper (arXiv:2512.07087v2) or the ETP Zulip thread up to 2026-10-14.
--
--   **Formalization Note** Automorphisms are elements of `Equiv.Perm E` with the property `∀ u w, f (opE u w) = opE (f u) (f w)` written out. The hypothesis is the disjunction of the two cases (with `Finite E` in the second), and the conclusion is (R) in the exact form of the hypothesis `hR` of (n), so it can be passed to (n) without rewriting (checked in Lean).
-- source:
--   Adam McKenna, 2026-10-20

import Definitions.Def_FiniteMagmaE677
import Mathlib

universe u
open FiniteMagmaE677

theorem FiniteMagmaE677.right_divisible_of_rigid_or_right_cancel
{E : Type u} (opE : E → E → E)
(hE : ((∀ α a b c : Equiv.Perm E,
    (∀ u w : E, α (opE u w) = opE (α u) (α w)) →
    (∀ u w : E, a (opE u w) = opE (a u) (a w)) →
    (∀ u w : E, b (opE u w) = opE (b u) (b w)) →
    (∀ u w : E, c (opE u w) = opE (c u) (c w)) →
    (∀ s t : E, s = opE t (opE (α s) (opE (opE (a t) (b s)) (c t)))) →
    α = 1 ∧ a = 1 ∧ b = 1 ∧ c = 1) ∧ FiniteMagmaE677.E255 opE) ∨
  (Finite E ∧ ∀ b : E, Function.Injective (fun a : E => opE a b))) :
∀ α a b c : Equiv.Perm E,
  (∀ u w : E, α (opE u w) = opE (α u) (α w)) →
  (∀ u w : E, a (opE u w) = opE (a u) (a w)) →
  (∀ u w : E, b (opE u w) = opE (b u) (b w)) →
  (∀ u w : E, c (opE u w) = opE (c u) (c w)) →
  (∀ s t : E, s = opE t (opE (α s) (opE (opE (a t) (b s)) (c t)))) →
  ∀ s : E, ∃ r : E, opE r (b s) = a s := by sorry
