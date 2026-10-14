-- Prove2me | Theorems.Thm_CorruptRobustRL_Supervised_lemma4_7_bellman_error_bound
-- name    : CorruptRobustRL.Supervised.lemma4_7_bellman_error_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T20:52:22.34739+00:00
-- url     : https://prove2.me/theorems/32c42843-6446-4113-9618-73439adcdfc3
-- title:
--   Lemma 4.7, p. 18 — with valid estimates, both Bellman errors are at most $\min(3H,2b+\max_{V\in\mathcal V_{h+1}}(\hat p-p^\star)^\top V)$, global and subsampled
-- statement:
--   Run UCBVI-BASE (Algorithm 2) for the nominal MDP with horizon $H\ge1$, with arbitrary active sets, any action selector, a global model-estimate $\mathfrak m_{\mathrm{gl}}=(\hat r_{\mathrm{gl}},\hat p_{\mathrm{gl}},b_{\mathrm{gl}})$ and a subsampled one $\mathfrak m_{\mathrm{sb}}=(\hat r_{\mathrm{sb}},\hat p_{\mathrm{sb}},b_{\mathrm{sb}})$, both with the tabular ranges, and let $\mathcal T$ be the resulting Q-supervisor. If both model-estimates are valid with respect to $\mathcal T$, then for every stage $h$, state $x$ and action $a$, with $\mathcal V_{h+1}=\{\bar V_{h+1}-V^\star_{h+1},\ \bar V_{h+1}-\underline V_{h+1}\}$,
--   $$\max\big(\overline{\mathbf{Bell}}_h(x,a),\ \overline{\mathbf{Bell}}_h(x,a)-\underline{\mathbf{Bell}}_h(x,a)\big)\le\min\Big(3H,\ 2b_{\mathrm{gl}}(x,a)+\max_{V\in\mathcal V_{h+1}}\big(\hat p_{\mathrm{gl}}(x,a)-p^\star(x,a)\big)^\top V\Big),$$
--   and the same bound holds with $(b_{\mathrm{sb}},\hat p_{\mathrm{sb}})$ in place of $(b_{\mathrm{gl}},\hat p_{\mathrm{gl}})$.
--
--   This converts the Bellman errors of Proposition 4.2 into bonuses plus transition-estimation errors, which are the terms $\Delta$ of Theorem 4.1.
--
--   **Formalization Note** The Q-supervisor is given as `T` with the hypothesis `T = ucbviSup H act gl sb sel`; the statement covers every learner $\ell$ of SuperVIsed.C, whose Q-supervisor is such a run.
-- source:
--   Lykouris, Simchowitz, Slivkins & Sun, Corruption-robust exploration in episodic reinforcement learning, arXiv:1911.08689v4, p. 18, Lemma 4.7; proof pp. 18–19

import Mathlib
import Definitions.Def_CorruptRobustRL_Supervised_MDP
import Definitions.Def_CorruptRobustRL_Supervised_Supervisor
import Definitions.Def_CorruptRobustRL_Supervised_Algorithm

namespace CorruptRobustRL.Supervised

open Finset QSupervisor

/-- Lemma 4.7 (p. 18): for a base learner (one run `𝒯` of UCBVI-BASE) whose global and subsampled
model-estimates are valid, `max(Bell̄_h, Bell̄_h − Bell̲_h) ≤ min(3H, 2b + max_{V ∈ 𝒱_{h+1}} (p̂ − p⋆)ᵀ V)`
for each of the two model-estimates, where `𝒱_{h+1} = {V̄_{h+1} − V⋆_{h+1}, V̄_{h+1} − V̲_{h+1}}`. -/
theorem lemma4_7_bellman_error_bound
    {X A : Type} [Fintype X] [DecidableEq X] [Fintype A] [DecidableEq A] [Nonempty A]
    (M : NominalMDP X A) (hM : M.IsNominal) (H : ℕ) (hH : 1 ≤ H)
    (act : ℕ → X → Finset A) (gl sb : ModelEst X A) (sel : Selector A)
    (T : QSupervisor X A) (hTdef : T = ucbviSup H act gl sb sel)
    (hgl : gl.IsModelEst H) (hsb : sb.IsModelEst H)
    (hvgl : gl.IsValid M H T) (hvsb : sb.IsValid M H T) :
    ∀ h < H, ∀ x a,
      max (upperBell M H T h x a) (upperBell M H T h x a - lowerBell M H T h x a) ≤
          min (3 * (H : ℝ)) (2 * gl.b x a +
            max (∑ x', (gl.p x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vstar M H (h + 1) x'))
                (∑ x', (gl.p x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vlow H T (h + 1) x'))) ∧
      max (upperBell M H T h x a) (upperBell M H T h x a - lowerBell M H T h x a) ≤
          min (3 * (H : ℝ)) (2 * sb.b x a +
            max (∑ x', (sb.p x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vstar M H (h + 1) x'))
                (∑ x', (sb.p x a x' - M.pstar x a x') * (Vbar H T (h + 1) x' - Vlow H T (h + 1) x'))) := by sorry

end CorruptRobustRL.Supervised
