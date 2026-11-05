-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_one_step_minimizer
-- name    : BauerleRiederMDP.LQ.one_step_minimizer
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:25:21.865299+00:00
-- url     : https://prove2.me/theorems/96c9fb5c-b0d8-446d-8928-0eb36cceca32
-- title:
--   §2.6.3 — the one-step LQ cost is convex in the action with unique minimizer $-(\mathbb E[B^\top QB])^{-1}\mathbb E[B^\top QA]\,x$
-- statement:
--   In the stochastic linear-quadratic problem under its standing assumptions, let $0\le n<N$ and let $v(x)=x^\top Qx$ with $Q$ symmetric positive definite. Fix a state $x\in\mathbb R^m$ and consider
--   $$
--   h(a)=x^\top Q_nx+\mathbb E\,v(A_{n+1}x+B_{n+1}a),\qquad a\in\mathbb R^d .
--   $$
--   Then:
--
--   1. $\mathbb E[B_{n+1}^\top QB_{n+1}]$ is positive definite and hence regular;
--   2. $h$ is convex;
--   3. the unique minimum point of $h$ is
--   $$
--   f^*_n(x)=-\big(\mathbb E[B_{n+1}^\top QB_{n+1}]\big)^{-1}\mathbb E[B_{n+1}^\top QA_{n+1}]\,x ,
--   $$
--   that is, $h(a)>h(f^*_n(x))$ for every $a\ne f^*_n(x)$.
--
--   This is the minimization inside one step of the Bellman recursion: it shows that the minimizers can be chosen linear in the state.
--
--   **Formalization Note** The expectation is under the law of $(A_{n+1},B_{n+1})$; it is a Bochner integral of a nonnegative quadratic polynomial in the entries, integrable by the square-integrability assumption.
--
--   Differences from the source:
--   - encoding: "the unique minimum point is $f^*_n(x)$" → $h(f^*_n(x))<h(a)$ for every $a\ne f^*_n(x)$; reason: the definition of a unique minimum point.
--   - encoding: "regular" → the determinant is a unit; reason: invertibility of a square matrix.
--   - encoding: "finite expectation and covariance" → every entry of $A_k$, $B_k$ square integrable, $k=1,\dots,N$; reason: same condition, on the indices the problem uses.
--   - encoding: $(\cdot)^{-1}$ → Mathlib's matrix inverse ($0$ on singular matrices); reason: the inverted matrix is positive definite under the hypotheses.
--   - encoding: $\mathbb E[\cdot]$ of a random matrix → entrywise Bochner integral under the law of $(A_{n+1},B_{n+1})$; reason: every entry is integrable under the square-integrability assumption, so it is the expectation.
--   - encoding: $\mathbb R^m$, $\mathbb R^d$ → `Fin m → ℝ`, `Fin d → ℝ`; reason: the same spaces.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §2.6.3, p.51 (PDF 66), unnumbered claim after the minimal cost operator

import Mathlib
import Definitions.Def_BauerleRiederMDP_LQ_Model
import Definitions.Def_BauerleRiederMDP_LQ_Riccati

open MeasureTheory ProbabilityTheory Matrix

namespace BauerleRiederMDP.LQ

/-- **§2.6.3, the one-step minimizer of the LQ problem** (Bäuerle & Rieder 2011, §2.6.3, p.51,
PDF 66, unnumbered claim): let `v(x) = x^⊤ Q x` with `Q` symmetric positive definite and
`0 ≤ n < N`. "Since `Q` is positive definite, we have by assumption that `𝔼[B_{n+1}^⊤ Q B_{n+1}]` is
also positive definite and thus regular and the function in brackets is convex in `a` (for fixed
`x ∈ E`). Differentiating with respect to `a` and setting the derivative equal to zero, we obtain
that the unique minimum point is given by
`f*_n(x) = −(𝔼[B_{n+1}^⊤ Q B_{n+1}])^{−1} 𝔼[B_{n+1}^⊤ Q A_{n+1}] x`."

Here the function in brackets is `a ↦ x^⊤ Q_n x + 𝔼 v(A_{n+1} x + B_{n+1} a)` (`LQData.costArg`),
and the conclusion states: `𝔼[B_{n+1}^⊤ Q B_{n+1}]` is positive definite and invertible; the
bracket is convex in `a`; and `f*_n(x)` is its unique minimum point (every other `a` gives a
strictly larger value).

**Formalization Note.** `E = Fin m → ℝ`, `A = Fin d → ℝ`; the expectation is under the law
`ν (n+1)` of `Z_{n+1} = (A_{n+1}, B_{n+1})`; `LQData.Standing` collects the standing assumptions of
§2.6.3. -/
theorem one_step_minimizer {m d N : ℕ} (M : LQData m d N) (hM : M.Standing) {n : ℕ} (hn : n < N)
    (Q : Matrix (Fin m) (Fin m) ℝ) (hQ : Q.PosDef) (x : Fin m → ℝ) :
    (M.EBQB n Q).PosDef ∧ IsUnit (M.EBQB n Q).det ∧
      ConvexOn ℝ Set.univ (fun a : Fin d → ℝ => M.costArg n Q x a) ∧
      ∀ a : Fin d → ℝ, a ≠ M.gainOf n Q *ᵥ x →
        M.costArg n Q x (M.gainOf n Q *ᵥ x) < M.costArg n Q x a := by sorry

end BauerleRiederMDP.LQ
