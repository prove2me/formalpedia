-- Prove2me | Theorems.Thm_FiniteSampleDependence_Rigidity_Supplement_four_task_restricted_deviations
-- name    : FiniteSampleDependence.Rigidity.Supplement.four_task_restricted_deviations
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T10:53:04.775203+00:00
-- url     : https://prove2.me/theorems/4e59cae1-12e7-4a2b-a10c-04562c29e214
-- title:
--   Theorem 7.3 — the four-task payment is truthful against deviations in $C_n$, $C_m$, and its truthful expectation is zero exactly at independence
-- statement:
--   Let $n,m\ge2$ (possibly unequal), and let both agents be paid the four-task payment $M_{\mathrm{QMI}}$ of equation (8). In the memoryless strategy model of §6, with signal distribution $P\in\Delta_{n,m}$ and report law $TPS^\top$:
--
--   1. for every $P\in\Delta_{n,m}$, every fixed column-stochastic Bob channel $S\in\mathbb R^{m\times m}$ and every Alice deviation $T\in C_n$,
--   $$\mathbb E_{(TPS^\top)^{\otimes4}}[M_{\mathrm{QMI}}]\le\mathbb E_{(PS^\top)^{\otimes4}}[M_{\mathrm{QMI}}];$$
--   2. for every $P\in\Delta_{n,m}$, every fixed column-stochastic Alice channel $T\in\mathbb R^{n\times n}$ and every Bob deviation $S\in C_m$,
--   $$\mathbb E_{(TPS^\top)^{\otimes4}}[M_{\mathrm{QMI}}]\le\mathbb E_{(TP)^{\otimes4}}[M_{\mathrm{QMI}}];$$
--   3. with both agents truthful, the common expected payment $\mathbb E_{P^{\otimes4}}[M_{\mathrm{QMI}}]$ is zero exactly when $\operatorname{rank}P=1$ (independence) and positive otherwise.
--
--   Here $C_n=\operatorname{conv}(DS_n\cup R1_n)$ is the convex hull of the doubly stochastic matrices and the signal-independent channels $q\mathbf 1_n^\top$. Only the agent's own deviation is restricted; the peer's channel is an arbitrary column-stochastic matrix. Four tasks therefore suffice for nontrivial rewards against restricted deviations for all alphabet sizes, in contrast with the $2n$-task bound of Theorem 6.2 against arbitrary channels.
--
--   Differences from the source:
--   - encoding: row indices 1..n, column indices 1..m → Fin n and Fin m (zero-based); reason: relabelling of indices; no instance changes
--   - encoding: the i.i.d. expectation E_{V^{⊗ℓ}}[M] of a payment rule → the exact finite sum Σ_{z ∈ ([n]×[m])^ℓ} M(z) ∏_t V_{x_t y_t} (expectedPayment), the paper's equation (6); reason: for finitely many outcomes the expectation is this sum; no measure-theoretic model is introduced
--   - encoding: independence of P → rank P = 1; reason: on Δ_{n,m} rank-one matrices are exactly the product distributions (§2)
--   - encoding: closing sentence 'Thus truthful reporting is a dominant strategy relative to the restricted own-deviation classes, even against unrestricted fixed memoryless strategies of the peer' → no separate clause; reason: the sentence restates clauses (i) and (ii)
-- source:
--   Yuqing Kong, Limits of Finite-Sample Dependence Measures under Data Processing Inequality, STOC 2027 submission #152 (October 2026; SHA-256 f5e620d74cb49d294e046590e96036aa28bf617d4b212a292b7bb68435363118), Theorem 7.3, PDF p. 19 (printed p. 18); payment (8), same page; C_n, §7.2, PDF p. 18

import Mathlib
import Definitions.Def_FiniteSampleDependence_Rigidity_Model
import Definitions.Def_FiniteSampleDependence_Rigidity_Supplement_Model

namespace FiniteSampleDependence.Rigidity.Supplement

open Matrix

/-- Theorem 7.3 (Four-task rewards under restricted deviations), PDF p. 19 (printed p. 18). For
every `n, m ≥ 2` the common payment rule (8) satisfies, in the memoryless strategy model:
(i) for every `P ∈ Δ_{n,m}` and every fixed (column-stochastic) Bob channel `S`, Alice's truthful
expected payment is at least her expected payment under any deviation `T ∈ C_n`;
(ii) symmetrically, for every fixed Alice channel `T`, Bob cannot gain by a deviation `S ∈ C_m`;
(iii) with both agents truthful, the common expected payment is zero exactly when `rank P = 1`
and positive otherwise. -/
theorem four_task_restricted_deviations {n m : ℕ} (hn : 2 ≤ n) (hm : 2 ≤ m) :
    (∀ P ∈ simplex n m, ∀ S : Matrix (Fin m) (Fin m) ℝ, IsColumnStochastic S →
      ∀ T ∈ restrictedChannels n,
        expectedPayment qmiPayment (T * P * Sᵀ) ≤ expectedPayment qmiPayment (P * Sᵀ)) ∧
    (∀ P ∈ simplex n m, ∀ T : Matrix (Fin n) (Fin n) ℝ, IsColumnStochastic T →
      ∀ S ∈ restrictedChannels m,
        expectedPayment qmiPayment (T * P * Sᵀ) ≤ expectedPayment qmiPayment (T * P)) ∧
    (∀ P ∈ simplex n m,
      (expectedPayment qmiPayment P = 0 ↔ P.rank = 1) ∧
        (P.rank ≠ 1 → 0 < expectedPayment qmiPayment P)) := by sorry

end FiniteSampleDependence.Rigidity.Supplement
