-- Prove2me | Theorems.Thm_CalibeatBandit_eq_3_1_solvable
-- name    : CalibeatBandit.eq_3_1_solvable
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:21.0772+00:00
-- url     : https://prove2.me/theorems/53680d9d-91f2-44d7-85d4-bad5aaf7aa53
-- title:
--   Equation (3.1) — the fixed-point equation always has a solution in $\Delta(\mathcal A)$
-- statement:
--   Let $\lambda\in[0,1]$, let $M^{\mathrm{SR}},M^{\mathrm{Rec}}$ be column-stochastic $K\times K$ matrices and $J\in\mathcal A$. Then there is a probability vector $p\in\Delta(\mathcal A)$ with
--   $$(I-\lambda M^{\mathrm{SR}})\,p=(1-\lambda)\,M^{\mathrm{Rec}}e_J .$$
--
--   This guarantees that the learner of Algorithm 1 can always choose a mixed strategy satisfying (3.1); the map $p\mapsto\lambda M^{\mathrm{SR}}p+(1-\lambda)M^{\mathrm{Rec}}e_J$ maps the simplex into itself.
--
--   **Formalization Note** $e_J$ is `Pi.single J 1`, $I$ is the identity matrix.
--
--   Differences from the source:
--   - generalization: the algorithm's $\lambda_t$ and column-stochastic $M^{\mathrm{SR}}_t,M^{\mathrm{Rec}}_t$ → every $\lambda\in[0,1]$ and all column-stochastic $M^{\mathrm{SR}},M^{\mathrm{Rec}}$; reason: the paper's Brouwer argument uses only these properties; the algorithm's quantities are instances
--   - encoding: actions $[K]$ → `Fin K`; reason: a relabelling
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §3, eq. (3.1) and the paragraph after (3.2), p.9 (PDF 9)

import Mathlib
import Definitions.Def_CalibeatBandit_IsColStochastic

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **Equation (3.1) always has a solution** (§3 "Choosing a mixed strategy", p.9).
For a mixing weight `λ ∈ [0, 1]`, column-stochastic `M^SR`, `M^Rec` and an action `J`, there is a
mixed strategy `p ∈ Δ(𝒜)` with `(I − λ M^SR) p = (1 − λ) M^Rec e_J`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §3, eq. (3.1) and the paragraph after (3.2), p.9.

**Formalization Note.** `e_J` is `Pi.single J 1`; `I` is the identity matrix `1`. The paper
states the claim for the algorithm's `λ_t` and `M^a_t`; it is stated here for every
`λ ∈ [0, 1]` and all column-stochastic matrices, which is what its Brouwer argument shows. -/
theorem eq_3_1_solvable {K : ℕ} (lam : ℝ) (hlam0 : 0 ≤ lam) (hlam1 : lam ≤ 1)
    (MSR MRec : Matrix (Fin K) (Fin K) ℝ) (hSR : IsColStochastic MSR)
    (hRec : IsColStochastic MRec) (J : Fin K) :
    ∃ p : Fin K → ℝ, IsProbVec p ∧
      (1 - lam • MSR) *ᵥ p = (1 - lam) • (MRec *ᵥ Pi.single J 1) := by sorry

end CalibeatBandit
