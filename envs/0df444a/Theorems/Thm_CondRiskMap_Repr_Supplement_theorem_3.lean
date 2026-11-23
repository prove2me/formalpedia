-- Prove2me | Theorems.Thm_CondRiskMap_Repr_Supplement_theorem_3
-- name    : CondRiskMap.Repr.Supplement.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T16:49:43.286951+00:00
-- url     : https://prove2.me/theorems/ecee3653-7986-46b1-874b-5f6205e0ef76
-- title:
--   Theorem 3 — finite-stage composite-envelope representation (5.9)–(5.10)
-- statement:
--   Let $T=n+1$ be any finite positive horizon and let $\mathcal F_1\subseteq\cdots\subseteq\mathcal F_T$ be a filtration on $\Omega$, with $\mathcal F_1=\{\varnothing,\Omega\}$ and $\mathcal F_T$ the final ambient sigma algebra. Let $\mathcal X_t,\mathcal Y_t$ be the corresponding nested paired locally convex function and finite signed-measure spaces, with evaluation-preserving function inclusions carrying the induced topologies and restriction-compatible measure inclusions. Identify the constant functions in $\mathcal X_1$ with $\mathbb R$. Assume (C) and (C′) at each adjacent pair. For $1\le\tau<T$, let $r_\tau:\mathcal X_{\tau+1}\to\mathcal X_\tau$ be positively homogeneous, lower semicontinuous conditional risk mappings satisfying (A1)–(A3). Suppose every $\mathcal X_t$, $2\le t\le T$, is separable.
--
--   For each $\tau$, let $\mathcal A_\tau(\omega)$ be the canonical conjugate-domain envelope from (3.8). These envelopes are probability-valued and weak* $\mathcal F_\tau$-measurable as multifunctions. For every $X\in\mathcal X_{\tau+1}$ and every $\omega$,
--
--   $$
--   [r_\tau(X)](\omega)=\sup_{\mu\in\mathcal A_\tau(\omega)}\langle\mu,X\rangle. \tag{5.10}
--   $$
--
--   Define $\rho_t=r_1\circ\cdots\circ r_{t-1}$. Form $\mathcal A_1\circ\cdots\circ\mathcal A_{t-1}$ by successive left-associated applications of (5.7): each composite consists of measures in the target $\mathcal Y_t$ satisfying the actual integral relation with an outer measure and a globally weak* measurable inner selection. Then, for every $2\le t\le T$, every $X\in\mathcal X_t$, and every $\omega\in\Omega$,
--
--   $$
--   \rho_t(X)=\sup_{\mu\in(\mathcal A_1\circ\cdots\circ\mathcal A_{t-1})(\omega)}\langle\mu,X\rangle. \tag{5.9}
--   $$
--
--   The left side is the constant value of the composed function, obtained directly from the identification $\mathcal X_1=\mathbb R$. Each supremum denotes a least upper bound of its actual real pairing values. This companion theorem extends the representation to every finite stage; Proposition 4 is its two-stage supporting result. It does not serve as a lemma of the published goal Theorem 2.
--
--   Differences from the source:
--   - encoding: the source indexes stages 1 through T and identifies the first function space with the reals → Lean indexes 0 through n, with T=n+1, and supplies the value-preserving linear equivalence; reason: the final real value is the constant function's value, without choosing an auxiliary probability measure or a sample point.
--   - reading: the source uses unparenthesized envelope composition and integrals in (5.7) → Lean specifies left association and requires those integral relations to be integrable; reason: p. 14 states associativity, and a fixed bracketing gives a precise expression without assuming associativity or closure in the paired measure space.
--   - encoding: the source uses real supremum notation in (5.9) and (5.10) → Lean asserts IsLUB of the actual real value sets; reason: this keeps the full finite-value claim without default suprema on empty or unbounded sets.
-- source:
--   Ruszczyński, Shapiro, Conditional risk mappings, preprint dated February 21, 2004, p. 14, Theorem 3; §5, pp. 12–14; standing paired spaces, (C), (C′), pp. 3–4.

import Mathlib
import Definitions.Def_CondRiskMap_Repr_Supplement_Setting

namespace CondRiskMap.Repr.Supplement

set_option autoImplicit false

/-- Theorem 3, p.14. All three assertions are retained: probability-valued weak*
measurable canonical one-step envelopes, their representation (5.10), and the
finite-stage composite-envelope representation (5.9), at every point. -/
theorem theorem_3 {Ω : Type*} {n : ℕ} (D : System Ω n)
    (hStanding : Standing D) (hRisk : RiskHypotheses D)
    (first : TrivialFirst D)
    (hSeparable : ∀ i : Fin n, TopologicalSpace.SeparableSpace (D.stage i.succ).X) :
    (∀ i : Fin n,
      WeakStarMultifunction (D.stage i.succ) (oneEnvelope D i) ∧
      (∀ ω, oneEnvelope D i ω ⊆
        @Prob Ω (D.stage i.succ).F _ _ _ _ _ _ _ _ (D.stage i.succ).P) ∧
      ∀ (X : (D.stage i.succ).X) (ω : Ω),
        IsLUB {r : ℝ | ∃ μ ∈ oneEnvelope D i ω, r = (D.stage i.succ).pairing μ X}
          ((D.stage i.succ).eval (upperRisk D i X) ω)) ∧
    (∀ (i : Fin (n+1)), 0 < i.val → ∀ (X : (D.stage i).X) (ω : Ω),
      IsLUB {r : ℝ | ∃ μ ∈ iteratedEnvelope D i ω, r = (D.stage i).pairing μ X}
        (first.value (riskToFirst D i X))) := by sorry

end CondRiskMap.Repr.Supplement
