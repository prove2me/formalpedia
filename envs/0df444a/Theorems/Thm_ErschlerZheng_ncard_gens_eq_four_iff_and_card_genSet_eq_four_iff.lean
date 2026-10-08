-- Prove2me | Theorems.Thm_ErschlerZheng_ncard_gens_eq_four_iff_and_card_genSet_eq_four_iff
-- name    : ErschlerZheng.ncard_gens_eq_four_iff_and_card_genSet_eq_four_iff
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-06T11:15:57.600466+00:00
-- url     : https://prove2.me/theorems/8f4b58bd-3f8d-4cce-aeb8-d0d426c1fb42
-- title:
--   Supporting fact for u_S in (7.11), not in the paper — a, b_ω, c_ω, d_ω are four distinct elements exactly when ω is not constant
-- statement:
--   For every string $\omega$ (`ω : ℕ → Fin 3`), the set $\{a, b_\omega, c_\omega, d_\omega\}$ of generators (`gens ω`, where $a$ is `Garrido.grigA` and $\gamma_\omega$ is `gen ω γ`) has four elements (`Set.ncard`) if and only if $\omega$ is not constant, that is, some $m, n$ have $\omega_m \neq \omega_n$. The same holds for the generating set $S$ as a subset of $G_\omega$ (`genSet ω`, a set of elements of `grigorchuk ω`, counted by `Nat.card`).
--
--   This is not a result of the paper. It backs the sentence of the Construction bundle note `ErschlerZheng_Construction` on $\mathbf u_S$ in (7.11): “$\mathbf u_S$ is `uniformMeasure (genSet ω)`, uniform on the distinct elements among $a, b_\omega, c_\omega, d_\omega$; when $\omega$ is not constant, as under Assumption $(\mathrm{Fr}(D))$, these are four distinct elements.” By definition `uniformMeasure (genSet ω)` puts mass `(Nat.card (genSet ω))⁻¹` on each element of `genSet ω`, so for a non-constant $\omega$ it is the paper's $\mathbf u_S$, with mass $1/4$ at each of $a, b_\omega, c_\omega, d_\omega$. That a string satisfying Assumption $(\mathrm{Fr}(D))$ is not constant is the fourth clause of `ErschlerZheng.exists_gt_eq_one_and_exists_gt_eq_two_and_tail_ne_and_not_eventually_const_and_exists_ne_of_satisfiesFr`.
-- source:
--   Erschler, A. and Zheng, T., Growth of periodic Grigorchuk groups, Invent. Math. 219 (2020) 1069–1155, https://doi.org/10.1007/s00222-019-00922-0 (arXiv:1802.09077v2, whose page numbers are used), p. 41, the four generators are distinct exactly when ω is not constant (supporting fact, not in the paper)

import Mathlib
import Definitions.Def_ErschlerZheng_Grigorchuk

namespace ErschlerZheng

theorem ncard_gens_eq_four_iff_and_card_genSet_eq_four_iff (ω : ℕ → Fin 3) :
    ((gens ω).ncard = 4 ↔ ∃ m n, ω m ≠ ω n) ∧ (Nat.card (genSet ω) = 4 ↔ ∃ m n, ω m ≠ ω n) := by
  sorry

end ErschlerZheng
