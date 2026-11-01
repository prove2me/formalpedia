-- Prove2me | Theorems.Thm_FocusSetRB_lemma_11
-- name    : FocusSetRB.lemma_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:18:18.906978+00:00
-- url     : https://prove2.me/theorems/dbbf2475-dd59-4ccb-9fa9-b9c1b7d1ac7b
-- title:
--   Lemma 11, p.42 — $W$ is well defined, positive definite, with eigenvalues $\ge1$
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1), and let $\Xi$ have every row equal to $\mu^*$. Then:
--
--   1. the series $W=\sum_{k\ge0}(P_{\bar\pi^*}-\Xi)^k(P_{\bar\pi^*}^\top-\Xi^\top)^k$ converges;
--   2. $W$ is positive definite;
--   3. every eigenvalue of $W$ is at least $1$, that is, $u\,u^\top\le u\,W\,u^\top$ for every row vector $u\in\mathbb R^{|\mathbb S|}$.
--
--   The lemma makes $\|\cdot\|_W$ a norm dominating the Euclidean norm, which is what the bounds of Lemmas 1 and 2 are measured in.
--
--   Differences from the source:
--   - encoding: W is well-defined → the series is Summable in Matrix S S ℝ; reason: "well-defined" means the infinite series converges
--   - encoding: eigenvalues of W lower bounded by 1 → u ⬝ᵥ u ≤ u ⬝ᵥ (W *ᵥ u) for every u; reason: equivalent for the symmetric matrix W
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Lemma 11, p.42 (Definition 2, eq. (30), pp.17, 42)

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_W

namespace FocusSetRB

open Matrix

/-- **Lemma 11, p.42** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4). The matrix `W` of Definition 2,
`W = ∑_{k≥0} (P_π̄* − Ξ)^k (P_π̄*ᵀ − Ξᵀ)^k`, is well defined; moreover `W` is positive definite with
eigenvalues lower bounded by `1`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** "Well defined" is the `Summable` clause (the series converges in
`Matrix S S ℝ`). "Eigenvalues lower bounded by 1" for the symmetric `W` is written as
`u uᵀ ≤ u W uᵀ` for every row vector `u`. -/
theorem lemma_11 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y)) :
    Summable (fun k : ℕ => (Ppi M y - Xi y) ^ k * ((Ppi M y)ᵀ - (Xi y)ᵀ) ^ k) ∧
    (W M y).PosDef ∧
    ∀ u : S → ℝ, u ⬝ᵥ u ≤ u ⬝ᵥ (W M y *ᵥ u) := by sorry

end FocusSetRB
