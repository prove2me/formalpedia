-- Prove2me | Theorems.Thm_ConvexRMDP_decomposition_4_5
-- name    : ConvexRMDP.decomposition_4_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:17:48.074596+00:00
-- url     : https://prove2.me/theorems/16dede6a-5aa5-4295-9056-f9676535cb4a
-- title:
--   §4.2, (4.5): $\tilde T = \log_b \circ \tilde t \circ \exp_b$ and $\tilde t$ maps $(\mathbb R^*_+)^S$ into itself
-- statement:
--   Let $(\mathcal S, \mathcal A, r, \gamma, \mathcal U)$ be an sa-rectangular robust MDP with $\mathcal A$ nonempty and let $b > 0$. Then:
--
--   1. for every $v \in \mathbb R^{\mathcal S}$,
--   $$
--   \tilde T(v) = \log_b \circ\, \tilde t \circ \exp_b(v),
--   $$
--   that is, $\tilde T(v)_s = \frac1b \log \tilde t\big((e^{b v_{s'}})_{s'}\big)_s$ for every $s$;
--   2. $\tilde t$ maps $(\mathbb R^*_+)^{\mathcal S}$ into $(\mathbb R^*_+)^{\mathcal S}$: if $x_s > 0$ for all $s$, then $\tilde t(x)_s > 0$ for all $s$.
--
--   Here $\tilde T$ is the regularized robust Bellman operator with uniform reference policy and $\tilde t$ is the operator (4.5), $\tilde t(x)_s = \sum_a \omega_b(s,a) \min_{p \in \mathcal U_{sa}} \prod_{s'} x_{s'}^{\gamma p_{s'}}$ with $\omega_b(s,a) = \exp(b\, r_{sa})/|\mathcal A|$.
--
--   The decomposition is what makes the feasible set $\{v \le \tilde T(v)\}$ convex after the change of variables $x = \exp_b(v)$.
--
--   Differences from the source:
--   - generalization: min over p ∈ 𝒰_sa (the paper's min presupposes attainment) → infimum (sInf) over an arbitrary nonempty 𝒰_sa ⊆ Δ(S); reason: the set is nonempty and bounded below; whenever the minimum is attained the infimum equals it, so the statement specializes to the source's.
--   - reading: 𝒰_sa ⊆ Δ(S) with min_{p ∈ 𝒰_sa} → 𝒰_sa nonempty (field U_nonempty of RMDP); reason: a minimum over an empty set is undefined; the paper's formulas presuppose nonemptiness.
--   - reading: A finite → A finite and nonempty; reason: Δ(A) is empty otherwise and the maximum in (4.1) is undefined.
--   - encoding: max over π_s ∈ Δ(A) in (4.1) → sSup over stdSimplex ℝ A; reason: the set is nonempty and bounded above and the maximum is attained (Lemma 4.1); same value.
--   - encoding: t̃ : (ℝ*₊)^S → (ℝ*₊)^S → a total function on S → ℝ with the typing as the positivity clause; reason: the formula agrees with the paper's on positive vectors, the only ones it is applied to.
-- source:
--   Grand-Clément & Petrik, On the Convex Formulations of Robust Markov Decision Processes, arXiv:2209.10187v2 (13 Dec 2023), §4.2, pp.12–13: the display chain on p.12 and (4.5) on p.13

import Mathlib
import Definitions.Def_ConvexRMDP_RMDP_regOp
import Definitions.Def_ConvexRMDP_RMDP_tOp

namespace ConvexRMDP

/-- **The decomposition `T̃ = log_b ∘ t̃ ∘ exp_b`** (Grand-Clément & Petrik, arXiv:2209.10187v2,
pp.12–13, the display chain ending in (4.5)): for every `v ∈ ℝ^S`,
`T̃(v) = log_b(t̃(exp_b(v)))` componentwise, and `t̃` maps `(ℝ*₊)^S` into `(ℝ*₊)^S`.

**Formalization Note.** `log_b(z) = log(z)/b` and `exp_b(z) = exp(b z)` (not `Real.logb`).
The typing `t̃ : (ℝ*₊)^S → (ℝ*₊)^S` of (4.5) is the second clause. `A` is nonempty and `b > 0`. -/
theorem decomposition_4_5 {S A : Type*} [Fintype S] [Fintype A] [Nonempty A]
    (M : RMDP S A) (b : ℝ) (hb : 0 < b) :
    (∀ v : S → ℝ, M.regOp b v = fun s => logB b (M.tOp b (fun s' => expB b (v s')) s)) ∧
      ∀ x : S → ℝ, (∀ s, 0 < x s) → ∀ s, 0 < M.tOp b x s := by sorry

end ConvexRMDP
