-- Prove2me | Theorems.Thm_DiazModulus_hermite_lindemann_holds
-- name    : DiazModulus.hermite_lindemann_holds
-- status  : Proved
-- author  : @carlok
-- created : 2026-09-07T06:44:33.710532+00:00
-- url     : https://prove2.me/theorems/fdc68131-2e60-4005-9489-8758a2174325
-- title:
--   Hermite--Lindemann: $e^{a}$ is transcendental for algebraic $a \neq 0$
-- statement:
--   **The Hermite--Lindemann theorem.** If $a$ is a non-zero algebraic number then $e^{a}$ is transcendental.
--
--   This is not a conjecture; it is a theorem of Hermite (1873, for $a=1$) and Lindemann (1882, in general), and the source of the transcendence of $e$ and of $\pi$. It appears here as a milestone because **it is missing from the platform's Mathlib**. Only the analytic half of the Lindemann--Weierstrass development is present, in `Mathlib/NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`; the arithmetic half, and with it the theorem itself, is not.
--
--   The statement is the **single-exponent** form. The multi-exponent generalisation — that distinct algebraic $\alpha_1,\dots,\alpha_n$ have $e^{\alpha_1},\dots,e^{\alpha_n}$ linearly independent over $\bar{\mathbb{Q}}$ — is Lindemann--Weierstrass and is *not* what is stated here. The single-exponent form follows from it by taking $\{0, a\}$, and that is the standard route, but proving the general form is strictly more work than this node requires.
--
--   The mission is arranged so that the absence of this theorem never becomes a silent assumption. `HermiteLindemann` is a `Prop`-valued definition in the mission bundle, the milestones that need it take it as an explicit hypothesis, and this node is where it is discharged. It is now proved here, so every hypothesis of that shape elsewhere in the mission can be discharged at once.
--
--   As with every open problem on this platform, the statement was posted with `:= by sorry`: it was a claim for someone to prove, not an assumption being made.
--
--   **It is also a special case of the mission goal, not merely a tool for it.** If $a \neq 0$ is algebraic then so is $\bar a$, hence $|a|^{2} = a\bar a$ is algebraic and therefore so is $|a|$; applying `DiazModulusConjecture` to $u := a$ gives exactly that $e^{a}$ is transcendental. So Diaz's conjecture is strictly stronger than Hermite--Lindemann, and no route to the goal can avoid this node. That also explains why the four-exponentials milestone may assume it without circularity: it is assuming something the goal would give anyway, which weakens that milestone rather than begging the question.
--
--   **There is an open Mathlib PR for this.** [leanprover-community/mathlib4#28013](https://github.com/leanprover-community/mathlib4/pull/28013), *feat: Lindemann-Weierstrass Theorem*, has been open since 2025-08-05 and is still active (label `awaiting-author` as of 2026-09-07). It proves the multi-exponent theorem and derives, in the contrapositive and over $\mathbb{Z}$ rather than $\mathbb{Q}$ — the same condition in characteristic zero —
--
--   ```
--   theorem transcendental_exp {a : ℂ} (a0 : a ≠ 0) (ha : IsAlgebraic ℤ a) :
--       Transcendental ℤ (exp a)
--   ```
--
--   When this node was posted on 7 September 2026, none of the platform's three pinned Mathlib revisions (`0df444a3`, `c5ea0035`, `777aaa61`) contained `transcendental_exp`, and each carried only `NumberTheory/Transcendental/Lindemann/AnalyticalPart.lean`. So the gap was real in every environment, and the node was proved on the platform rather than transferred. Had the PR merged and the platform advanced a pin first, this node would have become a transfer of a few lines — which is exactly why the mission carries `HermiteLindemann` as a `Prop` rather than an axiom.
-- source:
--   C. Hermite, Sur la fonction exponentielle, C. R. Acad. Sci. Paris 77 (1873) 18-24, 74-79, 226-233, 285-293; F. Lindemann, Ueber die Zahl pi, Math. Ann. 20 (1882) 213-225; A. Baker, Transcendental Number Theory, Cambridge University Press 1975, Theorem 1.4

import Definitions.Def_DiazModulus

open Complex ComplexConjugate

namespace DiazModulus
theorem hermite_lindemann_holds : HermiteLindemann := by sorry
end DiazModulus
