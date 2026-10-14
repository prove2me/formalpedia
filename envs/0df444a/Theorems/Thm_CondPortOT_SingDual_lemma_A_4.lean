-- Prove2me | Theorems.Thm_CondPortOT_SingDual_lemma_A_4
-- name    : CondPortOT.SingDual.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:12:55.223984+00:00
-- url     : https://prove2.me/theorems/fa63bac2-7e28-4b29-8a05-c792cb254459
-- title:
--   Lemma A.4, p. 36 — the fractional programs (19a) with Συᵢ ≥ εN and (19b) with Συᵢ = εN have equal values
-- statement:
--   Let $N\in\mathbb N$, $c\in\mathbb R^N$, $d\in\mathbb R^N_+$, $\varepsilon\in(0,1)$ and $\rho\in\mathbb R$. Consider
--   $$\text{(19a)}\quad \sup_{\upsilon\in[0,1]^N}\ \frac{\sum_i\upsilon_ic_i}{N\sum_i\upsilon_i}\quad\text{s.t.}\quad \sum_i\upsilon_i\ge\varepsilon N,\ \ \sum_i\upsilon_id_i\le\rho,$$
--   $$\text{(19b)}\quad \sup_{\upsilon\in[0,1]^N}\ \frac{\sum_i\upsilon_ic_i}{N\sum_i\upsilon_i}\quad\text{s.t.}\quad \sum_i\upsilon_i=\varepsilon N,\ \ \sum_i\upsilon_id_i\le\rho .$$
--   The optimal values of (19a) and (19b) are equal.
--
--   The lemma says the mass constraint may be tightened to an equality without loss, which is what makes the conditional expectation linear in the proof of Proposition A.5.
--
--   **Formalization Note** Values are suprema in $[-\infty,\infty]$; an infeasible program has value $-\infty$. The ratio is real division, which is never evaluated at a zero denominator on the feasible sets when $N\ge1$ (there $\sum_i\upsilon_i\ge\varepsilon N>0$); for $N=0$ both programs have the single feasible point of the empty index set. Indices are `Fin N`.
-- source:
--   Nguyen et al., Robustifying conditional portfolio decisions via optimal transport, arXiv:2103.16451v3, pp. 35–36, problems (19a)–(19b) and Lemma A.4

import Mathlib
import Definitions.Def_CondPortOT_SingDual_Setting

open MeasureTheory

namespace CondPortOT.SingDual

theorem lemma_A_4 (N : ℕ) (c d : Fin N → ℝ) (hd : ∀ i, 0 ≤ d i) (ε : ℝ) (hε0 : 0 < ε)
    (hε1 : ε < 1) (ρ : ℝ) :
    (⨆ (υ : Fin N → ℝ) (_ : (∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ ε * N ≤ ∑ i, υ i ∧
        ∑ i, υ i * d i ≤ ρ),
        (((∑ i, υ i * c i) / (N * ∑ i, υ i) : ℝ) : EReal)) =
      ⨆ (υ : Fin N → ℝ) (_ : (∀ i, υ i ∈ Set.Icc (0 : ℝ) 1) ∧ ∑ i, υ i = ε * N ∧
        ∑ i, υ i * d i ≤ ρ),
        (((∑ i, υ i * c i) / (N * ∑ i, υ i) : ℝ) : EReal) := by sorry

end CondPortOT.SingDual
