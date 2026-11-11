-- Prove2me | Theorems.Thm_EntAssistOneWay_Separation_theorem_3_5
-- name    : EntAssistOneWay.Separation.theorem_3_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-10T20:46:46.658402+00:00
-- url     : https://prove2.me/theorems/da4a4e0b-7661-4d40-9232-90580f9b3b5c
-- title:
--   Theorem 3.5 — remote preparation of flat states
-- statement:
--   There is an absolute constant $c>0$ such that for every $1\le r\le d$ and $\varepsilon>0$, a one-way protocol using exactly $\lceil\log_2d\rceil$ EPR pairs prepares every rank-$r$ flat state $P/r$ with trace error strictly less than $\varepsilon$, except with probability at most $\varepsilon$. Its number $C$ of classical bits satisfies
--   $$C\le\log_2(d/r)+c\log_2\!\bigl(1/\min\{\varepsilon,1/2\}\bigr).$$
--   This is the external preparation result cited as Theorem 1.2 of [KL26a], providing the preparation task needed for subgroup membership. The paper writes $O(\log(1/\varepsilon))$; $c$ is chosen before $d,r,\varepsilon$. For $\varepsilon>1/2$, the bound retains the protocol for tolerance $1/2$.
--
--   Differences from the source:
--   - reading: the trace-error convention in Definition 3.1 is denoted by ‖·‖tr → full Schatten-1 norm; reason: the inequality on p. 22 requires the full norm; this is the stronger reading
--   - reading: log(d/r) + O(log(1/ε)) without a specified ε range → log₂(d/r) + c log₂(1/min(ε,1/2)) for every ε > 0; reason: the expression agrees for 0 < ε ≤ 1/2 and extends to larger tolerances by monotonicity
--   - encoding: P/r for a rank-r projector → 1 ≤ r ≤ d; reason: rank zero leaves the source target P/r undefined
--   - encoding: ⌈log₂ d⌉ shared EPR pairs → the fixed Φ_E state, without an extra public seed; reason: exact EPR resources are counted and any private operations are POVMs or channels
-- source:
--   Ryan Anselm, Srijita Kundu, Olivier Lalonde, Ashwin Nayak, STOC 2027 submission #228 (October 2026), p. 19, Theorem 3.5 and Definition 3.1

import Definitions.Def_EntAssistOneWay_Separation_RemotePreparation

open scoped BigOperators ComplexOrder
open Classical
set_option autoImplicit false

namespace EntAssistOneWay.Separation

noncomputable section

/-- Theorem 3.5, p. 19; the ε > 1/2 regime uses the ε = 1/2 protocol. -/
theorem theorem_3_5 :
    ∃ c : ℝ, 0 < c ∧ ∀ (d r : ℕ), 1 ≤ r → r ≤ d →
      ∀ ε : ℝ, 0 < ε → ∃ (C : ℕ) (P : RemotePreparation d r (logCeil d) C),
        (C : ℝ) ≤ log₂ ((d : ℝ) / r) + c * log₂ (1 / min ε (1 / 2)) ∧
        PreparesFlat P ε := by sorry

end

end EntAssistOneWay.Separation
