-- Prove2me | Theorems.Thm_CondRiskMap_Repr_Supplement_proposition_4
-- name    : CondRiskMap.Repr.Supplement.proposition_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T12:22:16.184172+00:00
-- url     : https://prove2.me/theorems/6a598b11-3322-4927-a27e-e6ea5606ebef
-- title:
--   Proposition 4 — two-stage integral representation (5.4)
-- statement:
--   Let $\mathcal F_1\subseteq\mathcal F_2\subseteq\mathcal F_3$ be sigma algebras on $\Omega$, with nested paired locally convex function and finite signed-measure spaces $\mathcal X_j,\mathcal Y_j$. Function-space inclusions carry the induced topology and preserve evaluation; measure-space inclusions preserve restriction. Assume the standing conditions (C) and (C′) at each adjacent pair. Let $r_1:\mathcal X_2\to\mathcal X_1$ and $r_2:\mathcal X_3\to\mathcal X_2$ be lower semicontinuous, positively homogeneous conditional risk mappings satisfying (A1)–(A3), and suppose only $\mathcal X_3$ is separable. Write $\mathcal A_j(\omega)$ for the canonical conjugate-domain envelope of $r_j$, and $\langle\mu,X\rangle=\int X\,d\mu$ for the signed integral pairing.
--
--   For every $X\in\mathcal X_3$ and every $\omega\in\Omega$, all scalar functions $z\mapsto\langle\kappa(z),X\rangle$, for $\mu_1\in\mathcal A_1(\omega)$ and globally weak* $\mathcal F_2$-measurable selections $\kappa(z)\in\mathcal A_2(z)$, are integrable against $|\mu_1|$, and
--
--   $$
--   [r_1(r_2(X))](\omega)=\sup_{\mu_1\in\mathcal A_1(\omega)}\ \sup_{\kappa(\cdot)\in\mathcal A_2(\cdot)}
--   \int_\Omega\langle\kappa(z),X\rangle\,d\mu_1(z). \tag{5.4}
--   $$
--
--   The inner supremum ranges over those entire measurable selections, with a single selection used throughout each integral. This is the two-stage representation supporting Theorem 3. The displayed finite value is the least upper bound of the set of all displayed integral values.
--
--   Differences from the source:
--   - reading: the source writes the integrals in (5.4) without an explicit integrability clause → Lean also asserts integrability for every allowed selection; reason: this makes existence of the displayed integrals a conclusion and prevents undefined real integrals from returning zero, without excluding any selection.
--   - encoding: the source uses a double real supremum and stages 1, 2, 3 → Lean uses IsLUB of the same real value set and indices 0, 1, 2; reason: IsLUB retains the finite supremum assertion even for potentially empty or unbounded indexing sets, and zero-based indices avoid truncated subtraction.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, p. 12, Proposition 4; §5, pp. 12–14; standing paired spaces, (C), (C′), pp. 3–4.

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Supplement_Setting

namespace CondRiskMap.Repr.Supplement

set_option autoImplicit false

/-- Proposition 4, p.12, (5.4). The first conjunct records existence of the actual
integrals for ALL globally weak* measurable selections, rather than giving a
nonintegrable Bochner integral its default value. Only the final space is separable. -/
theorem proposition_4 {Ω : Type*} (D : System Ω 2)
    (hStanding : Standing D) (hRisk : RiskHypotheses D)
    [TopologicalSpace.SeparableSpace (D.stage 2).X] :
    ∀ (X : (D.stage 2).X) (ω : Ω),
      (∀ μ ∈ oneEnvelope D 0 ω, ∀ κ : Ω → (D.stage 2).Y,
        OneSelection D 1 κ →
        (D.stage 1).ScalarIntegrable μ (fun z => (D.stage 2).pairing (κ z) X)) ∧
      IsLUB {r : ℝ | ∃ μ ∈ oneEnvelope D 0 ω, ∃ κ : Ω → (D.stage 2).Y,
        OneSelection D 1 κ ∧ r =
          (D.stage 1).integral μ (fun z => (D.stage 2).pairing (κ z) X)}
        ((D.stage 0).eval (D.risk 0 (D.risk 1 X)) ω) := by sorry

end CondRiskMap.Repr.Supplement
