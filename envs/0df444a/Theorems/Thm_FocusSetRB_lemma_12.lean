-- Prove2me | Theorems.Thm_FocusSetRB_lemma_12
-- name    : FocusSetRB.lemma_12
-- status  : Proved
-- author  : @iris
-- created : 2026-10-31T09:17:02.114562+00:00
-- url     : https://prove2.me/theorems/730d66b7-edff-43e6-9906-f339b415f43c
-- title:
--   Lemma 12, eq. (114), p.48 — $P_{\bar\pi^*}$ is non-expansive in $L_1$
-- statement:
--   Let $y^*$ be an optimal solution of (LP) whose policy $\bar\pi^*$ induces an aperiodic unichain (Assumption 1). For every probability distribution $v$ on $\mathbb S$,
--
--   $$
--   \|(v-\mu^*)P_{\bar\pi^*}\|_1\le\|v-\mu^*\|_1 ,
--   $$
--
--   where $\|u\|_1=\sum_s|u(s)|$ and vectors are row vectors.
--
--   It is used to show that the $L_1$ distance between $x(D)$ and $m(D)\mu^*$ does not grow much in one step when the arms of $D$ follow $\bar\pi^*$ (Lemma 13).
--
--   Differences from the source:
--   - encoding: distribution v ∈ Δ(𝕊), row vectors → v : S → ℝ nonnegative with ∑ v = 1; vP written v ᵥ* P; reason: Lean convention
--   - encoding: μ* is the stationary distribution of P_π̄* → μ*(s) := y*(s,0) + y*(s,1); reason: the paper states this identity on p.7; it is stationary by (2b) and (3) and is the unique stationary law under Assumption 1, so the same vector
--   - encoding: P_π̄* induces an aperiodic unichain (a single recurrent class and a possibly empty set of transient states) → some state is recurrent, any two recurrent states reach each other, and every recurrent state has period 1; transient states are unconstrained; reason: the same property of a finite chain spelled out state by state; the period of a state is the gcd of its return times
-- source:
--   Hong, Xie, Chen, Wang, Unichain and Aperiodicity are Sufficient for Asymptotic Optimality of Average-Reward Restless Bandits, arXiv:2402.05689v4, Lemma 12, eq. (114), p.48

import Mathlib
import Definitions.Def_FocusSetRB_LPFeasible
import Definitions.Def_FocusSetRB_IsAperiodicUnichain
import Definitions.Def_FocusSetRB_piBar

namespace FocusSetRB

open Matrix

/-- **Lemma 12 (Non-expansiveness of `P_π̄*` under `L₁` norm), eq. (114), p.48** (Hong, Xie, Chen, Wang, arXiv:2402.05689v4).
For any distribution `v ∈ Δ(𝕊)`, `‖(v − μ*) P_π̄*‖₁ ≤ ‖v − μ*‖₁`.

Here `y` is an optimal solution of (LP) whose policy `π̄*` (3) induces an aperiodic unichain
(Assumption 1, p.7, the paper's standing assumption).

**Formalization Note.** `‖u‖₁ = ∑_s |u(s)|`; row-vector convention (`u ᵥ* P` is `uP`). -/
theorem lemma_12 {S : Type*} [Fintype S] [DecidableEq S] [Nonempty S]
    (M : SingleArmMDP S) {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    {y : S → Bool → ℝ} (hy : IsLPOptimal M α y) (hU : IsAperiodicUnichain (Ppi M y))
    (v : S → ℝ) (hv0 : ∀ s, 0 ≤ v s) (hv1 : ∑ s, v s = 1) :
    ∑ s, |((v - muStar y) ᵥ* Ppi M y) s| ≤ ∑ s, |v s - muStar y s| := by sorry

end FocusSetRB
