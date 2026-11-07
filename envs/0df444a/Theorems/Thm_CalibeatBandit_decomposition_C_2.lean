-- Prove2me | Theorems.Thm_CalibeatBandit_decomposition_C_2
-- name    : CalibeatBandit.decomposition_C_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:41:00.350205+00:00
-- url     : https://prove2.me/theorems/bf8f6311-e6f4-4bfb-abd2-386afb1ec088
-- title:
--   §C.2 (p.32) — three-part decomposition of $R^{\mathrm{SR},p}_T$ and $R^{\mathrm{Rec},p}_T$
-- statement:
--   Let $0\le\mu\le1$, let $x_t\in\Delta(\mathcal A)$, $y_t\in[0,1]^K$, $v_t\in\mathbb R^K$ and $J_t\in\mathcal A$ for $t=1,\dots,T$, and let $p_t=(1-\mu)x_t+\mu u$ with $u=\frac1K\mathbf 1$. Then
--   $$R^{\mathrm{SR},p}_T\le\mu T+\max_f\sum_{t=1}^T\Bigl(\sum_ix_t(i)v_t(f(i))-\langle x_t,v_t\rangle\Bigr)+\max_f\sum_{t=1}^T\sum_ix_t(i)\bigl(y_t(f(i))-v_t(f(i))\bigr)+\sum_{t=1}^T\langle x_t,v_t-y_t\rangle$$
--   and
--   $$R^{\mathrm{Rec},p}_T\le\mu T+\max_f\sum_{t=1}^T\bigl(v_t(f(J_t))-\langle x_t,v_t\rangle\bigr)+\max_f\sum_{t=1}^T\bigl(y_t(f(J_t))-v_t(f(J_t))\bigr)+\sum_{t=1}^T\langle x_t,v_t-y_t\rangle ,$$
--   where $f$ ranges over all maps $\mathcal A\to\mathcal A$.
--
--   The four terms are the exploration loss, the regret on corrected rewards (Lemma C.3), the estimation loss (Lemma C.4) and the correction loss (Lemma C.5).
--
--   **Formalization Note** The inequalities are deterministic; $p_t$ is constrained only on the rounds $0,\dots,T-1$.
--
--   Differences from the source:
--   - generalization: the algorithm's $x_t$, $v_t$, $J_t$ with $0<\mu\le1/2$ → arbitrary $x_t\in\Delta(\mathcal A)$, $v_t\in\mathbb R^K$, $J_t$ and $0\le\mu\le1$; reason: the algorithm's quantities satisfy these hypotheses
--   - encoding: rounds $t=1,\dots,T$, actions $\mathcal A=[K]$ → rounds $t=0,\dots,T-1$ (`Finset.range T`), actions `Fin K`; reason: a relabelling; same instances
-- source:
--   Hartline, Wang, Wu, Calibeating Bandit Advice (manuscript, STOC 2027 submission, sha256 a65ccb0880e6e4698eee1717d9a7121019b84a5ebcb4dfaa2e1614dbd3de0b44), §C.2, the two displays before Lemma C.3, p.32 (PDF 32)

import Mathlib
import Definitions.Def_CalibeatBandit_IsProbVec
import Definitions.Def_CalibeatBandit_pseudoSwapRegret
import Definitions.Def_CalibeatBandit_pseudoRewardLoss

set_option autoImplicit false

open MeasureTheory Matrix

namespace CalibeatBandit

/-- **The three-part decomposition of the pseudo regrets** (§C.2, p.32). Let
`p_t = (1 − μ) x_t + μ u` with `x_t ∈ Δ(𝒜)`, `u = (1/K)·𝟏`, `0 ≤ μ ≤ 1`, rewards
`y_t ∈ [0,1]^K`, arbitrary vectors `v_t` and actions `J_t`. Then
`R^{SR,p}_T ≤ μT + max_f ∑_t (∑_i x_t(i) v_t(f(i)) − ⟨x_t, v_t⟩)
  + max_f ∑_t ∑_i x_t(i)(y_t(f(i)) − v_t(f(i))) + ∑_t ⟨x_t, v_t − y_t⟩`
and
`R^{Rec,p}_T ≤ μT + max_f ∑_t (v_t(f(J_t)) − ⟨x_t, v_t⟩) + max_f ∑_t (y_t(f(J_t)) − v_t(f(J_t)))
  + ∑_t ⟨x_t, v_t − y_t⟩`.

Hartline, Wang, Wu, *Calibeating Bandit Advice* (manuscript, sha256 a65ccb08…), §C.2, p.32 (the two displays before Lemma C.3).

**Formalization Note.** Deterministic: the inequalities hold for every realization. The paper
states them for the algorithm's `x_t`, `v_t` with `0 < μ ≤ 1/2`; here `x`, `v`, `J` are arbitrary
(with `x_t ∈ Δ(𝒜)`) and `0 ≤ μ ≤ 1`. Rounds are `0, …, T − 1`; `p` is only constrained on
those rounds. -/
theorem decomposition_C_2 {K T : ℕ} (μ : ℝ) (hμ0 : 0 ≤ μ) (hμ1 : μ ≤ 1)
    (x v y p : ℕ → Fin K → ℝ) (J : ℕ → Fin K) (hx : ∀ t < T, IsProbVec (x t))
    (hy : ∀ t < T, ∀ j, y t j ∈ Set.Icc (0 : ℝ) 1)
    (hp : ∀ t < T, ∀ j, p t j = (1 - μ) * x t j + μ / K) :
    pseudoSwapRegret T p y ≤ μ * T
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, (∑ i, x t i * v t (f i) - x t ⬝ᵥ v t))
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, ∑ i, x t i * (y t (f i) - v t (f i)))
        + ∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t) ∧
    pseudoRewardLoss T p y J ≤ μ * T
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, (v t (f (J t)) - x t ⬝ᵥ v t))
        + Finset.univ.sup' ⟨id, Finset.mem_univ _⟩ (fun f : Fin K → Fin K =>
            ∑ t ∈ Finset.range T, (y t (f (J t)) - v t (f (J t))))
        + ∑ t ∈ Finset.range T, x t ⬝ᵥ (v t - y t) := by sorry

end CalibeatBandit
