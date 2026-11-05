-- Prove2me | Theorems.Thm_BauerleRiederMDP_Indifference_eq_4_39
-- name    : BauerleRiederMDP.Indifference.eq_4_39
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:28:52.26766+00:00
-- url     : https://prove2.me/theorems/d56e50a5-ebd5-45b7-88d2-c041be70360c
-- title:
--   (4.39) — the problem defining $v$ has an optimal solution, and $v$ is positive and finite
-- statement:
--   Under Assumption (FM) the infimum
--   $$
--   v=\inf_{a\in\mathbb R}\mathbb E\bigl[e^{-\gamma a(\tilde R_1-1)}\bigr]
--   $$
--   of (4.39) is attained at some $a\in\mathbb R$, and $v$ is positive and finite.
--
--   This is the base of the formula $V^0_n(x,s,\hat s)=-e^{-\gamma x}v^{N-n}$ and what gives meaning to the division by $v^{N-n}$ in Theorem 4.9.4 b).
--
--   **Formalization Note** $v$ is a real number, which is the finiteness.
--
--   Differences from the source: none.
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, sentence after eq. (4.39), p.138

import Mathlib
import Definitions.Def_BauerleRiederMDP_Indifference_Market_v

open MeasureTheory

namespace BauerleRiederMDP.Indifference

/-- Under (FM) the problem (4.39) has an optimal solution and its value `v` is positive and finite
(Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), §4.9, eq. (4.39),
p.138, PDF 152).

**Formalization Note.** `v` is a real number, which is the finiteness. -/
theorem eq_4_39 (M : Market) :
    (∃ a : ℝ, ∫ ω, Real.exp (-M.γ * a * (M.Rt ω - 1)) ∂M.P = M.v) ∧ 0 < M.v := by sorry

end BauerleRiederMDP.Indifference
