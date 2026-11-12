-- Prove2me | Theorems.Thm_FasterWCTFPTAS_Main_observation_4_5
-- name    : FasterWCTFPTAS.Main.observation_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T07:06:35.490188+00:00
-- url     : https://prove2.me/theorems/85d815f2-e465-4b03-96d5-3929d712ba5a
-- title:
--   Observation 4.5 — OPT ≥ U/m
-- statement:
--   Fix $m\ge2$ machines and a sorted instance ($w_1/p_1\ge\dots\ge w_n/p_n$) with $p_j>0$, $w_j\ge0$. With $T_j=\sum_{l\le j}p_l$ and $U=\sum_{j=1}^nw_jT_j$ (the optimal single-machine cost),
--
--   $$
--   \mathrm{OPT}\ge\frac{U}{m}.
--   $$
--
--   This lower bound converts the additive error $\delta(A\cdot X+B)$ of relaxed representative sets into a multiple of $\mathrm{OPT}$ in Lemma 4.6.
--
--   Differences from the source:
--   - encoding: OPT ≔ min over partitions processed in increasing index order of the sorted instance → OPT m p w, the minimum over all nonpreemptive schedules (assignment and any per-machine order); reason: on a sorted instance (a hypothesis here) the two minima coincide by Smith's rule, which §4 invokes
--   - generalization: §4: integer processing times p_j > 0 and integer weights w_j ≥ 0 → real p_j > 0 and real w_j ≥ 0; reason: §1 (p. 1) states the problem for real data; integer instances are a special case
-- source:
--   Karl Bringmann, Anita Dürr, Karol Węgrzycki, STOC 2027 submission #1072 (October 2026), p. 14 (PDF p. 15), Observation 4.5

import Mathlib
import Definitions.Def_FasterWCTFPTAS_Main_Scheduling

set_option autoImplicit false

namespace FasterWCTFPTAS.Main

/-- Observation 4.5, p. 14 (PDF 15): `OPT ≥ U/m`, where `U = U_n = Σ_{j=1}^n w_j T_j`.
Hypotheses: §4's standing assumptions (`m ≥ 2`, `p_j > 0`, jobs sorted by Smith's ratio). -/
theorem observation_4_5 {m n : ℕ} (hm : 2 ≤ m) (p w : Fin n → ℝ) (hp : ∀ j, 0 < p j) (hw : ∀ j, 0 ≤ w j)
    (hsort : Sorted p w) :
    U p w n / m ≤ OPT m p w := by sorry

end FasterWCTFPTAS.Main
