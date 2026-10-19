-- Prove2me | Theorems.Thm_DigitalPrivacy_Welfare_theorem_2
-- name    : DigitalPrivacy.Welfare.theorem_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:45.162986+00:00
-- url     : https://prove2.me/theorems/444a7e5f-2575-4dcd-a931-dcb141fcb2be
-- title:
--   Theorem 2, p. 13 — a usage-driven business under-collects and under-protects; with P > 0 it never under-collects while over-protecting
-- statement:
--   Work in the model of *DigitalPrivacy.Welfare.Setting* under the standing assumptions $0\le\beta<1$, $0\le\rho<1$, $\psi>0$, $0\le P\le1$, $0<\alpha\le1$. Let $(\xi^*,C^*)$ be any business optimum, a feasible maximizer of the profit $\Pi(\xi,C)=(1-P)\bar a^*+P\xi\bar a^*-\psi C$, and let $(\xi^W,C^W)$ be any social optimum, a feasible maximizer of $W=\alpha\,\mathrm{CS}+(1-\alpha)\Pi$ (problem (7)). Then:
--
--   1. if the business is purely usage-driven ($P=0$), it under-collects and under-protects users' data:
--   $$
--   \xi^*\le\xi^W\quad\text{and}\quad C^*\le C^W;
--   $$
--   2. if the business's revenue has a data-driven component ($P>0$), it never under-collects and over-protects: it is not the case that
--   $$
--   \xi^*\le\xi^W\quad\text{and}\quad C^*\ge C^W
--   $$
--   with at least one of the two inequalities strict.
--
--   These are the first two sentences of Theorem 2. They identify the one direction of misalignment between a monopolist's data strategy and the socially optimal one that no revenue model produces, and show that a purely usage-driven business errs on the side of too little data protection.
--
--   **Formalization Note.** The statement holds for every pair of optima; neither existence nor uniqueness is asserted. Two hypotheses are added to the printed ranges: $\psi>0$ (with $\psi=0$, $\rho=0$, $P=0$ both optima are $(0,C)$ for any $C$ and part 1 fails) and $\alpha>0$ (with $\alpha=0$ the planner's problem is the business's and the paper's argument does not apply). The third sentence of Theorem 2 ("any other direction … is the outcome for some specification") is established numerically in the paper and is not part of this statement.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 13, Theorem 2, first two sentences (proof App. A.4, pp. 33–35)

import Mathlib
import Definitions.Def_DigitalPrivacy_Welfare_Setting

namespace DigitalPrivacy.Welfare
theorem theorem_2 (β ρ ψ P α : ℝ) (h : Standing β ρ ψ P α) (ξs Cs ξW CW : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ P ξs Cs) (hW : IsSocialOpt β ρ ψ P α ξW CW) :
    (P = 0 → ξs ≤ ξW ∧ Cs ≤ CW) ∧
      (0 < P → ¬ (ξs ≤ ξW ∧ CW ≤ Cs ∧ (ξs < ξW ∨ CW < Cs))) := by sorry
end DigitalPrivacy.Welfare
