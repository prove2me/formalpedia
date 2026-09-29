-- Prove2me | Theorems.Thm_AutomorphicForm_summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le
-- name    : AutomorphicForm.summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/5f2b494a-066b-5a80-91cb-edb1c500fb90
-- title:
--   Polynomial sparsity of spreads gives summable archimedean weights
-- statement:
--   Let $V$ be a non-empty finite type, let $\iota_E$ be an index type equipped with a function $n_E \colon \iota_E \to \mathbb{N}$, let $\tau, \tau' \colon \iota_E \to V \to \mathbb{R}$ be two families of real parameter vectors indexed by $V$, and let $C \in \mathbb{R}$ and $d \in \mathbb{N}$. For $e \in \iota_E$ write $\operatorname{spread}(e) = \sum_{v}\sum_{v'} |\tau_e(v) - \tau_e(v')|$, and call $e$ charged when $n_E(e) > 0$. Assume the polynomial counting hypothesis: for every real $R \ge 0$ the set of charged $e$ with $\operatorname{spread}(e) \le R$ is finite, and its cardinality, viewed as a real number, is at most $C(1+R)^d$. The conclusion asserts that for every natural number $B$ with $d + 3 \le B$ both of the following families are summable over $\iota_E$: the family whose value at charged $e$ is $\int_{\mathbb{R}} \bigl(1 + \sum_{v}(|t + \tau_e(v)| + |t - \tau'_e(v)|)\bigr)^{-B}\,dt$ and whose value at uncharged $e$ is $0$; and the family whose value at charged $e$ is $\bigl(1 + \sum_{v}(|\tau_e(v)| + |\tau'_e(v)|)\bigr)^{-B}$ and whose value at uncharged $e$ is $0$. The exponent $-B$ is taken as a real power.
--
--   This is a purely real-analytic counting and summation estimate: polynomial growth of the number of parameter vectors of bounded spread modulo the diagonal forces convergence of the associated archimedean weights, both in integrated and in pointwise form. It is used in the construction of integrable archimedean parameters for unitary characters with pairwise distinct components, where the summability over the continuous index set must be established.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le.lean

import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_LanglandsTunnell_ConverseData

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain AutomorphicForm

theorem AutomorphicForm.summable_integral_rpow_neg_and_summable_rpow_neg_of_ncard_spread_le
    (V : Type) [Fintype V] [Nonempty V] (ιE : Type) (nE : ιE → ℕ)
    (τ τ' : ιE → V → ℝ) (C : ℝ) (d : ℕ)
    (hcount : ∀ R : ℝ, 0 ≤ R →
      {e : ιE | 0 < nE e ∧ ∑ v : V, ∑ v' : V, |τ e v - τ e v'| ≤ R}.Finite ∧
      (({e : ιE | 0 < nE e ∧ ∑ v : V, ∑ v' : V, |τ e v - τ e v'| ≤ R}.ncard : ℕ) : ℝ) ≤ C * (1 + R) ^ d) :
    ∀ B : ℕ, d + 3 ≤ B →
      Summable (fun e : ιE => if 0 < nE e then
        ∫ t : ℝ, (1 + ∑ v : V, (|t + τ e v| + |t - τ' e v|)) ^ (-(B : ℝ)) else 0) ∧
      Summable (fun e : ιE => if 0 < nE e then
        (1 + ∑ v : V, (|τ e v| + |τ' e v|)) ^ (-(B : ℝ)) else 0) := by sorry
