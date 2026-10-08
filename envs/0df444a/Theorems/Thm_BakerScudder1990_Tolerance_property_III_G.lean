-- Prove2me | Theorems.Thm_BakerScudder1990_Tolerance_property_III_G
-- name    : BakerScudder1990.Tolerance.property_III_G
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T06:10:40.194173+00:00
-- url     : https://prove2.me/theorems/0187e6bc-4329-41be-a58c-015540016f2b
-- title:
--   Property III(G) — the least optimal due date puts some job at an end of its tolerance window
-- statement:
--   Consider an instance of the single-machine common-due-date model with tolerances and $n \ge 1$ jobs in a fixed sequence, processed without inserted idle time, with completion times $C_1,\dots,C_n$ and total penalty $f(d)$ as a function of the common due date $d$. Then a least optimal due date exists, and at the least optimal due date $d$ some job $j$ completes at an end of its tolerance window:
--
--   $$
--   C_j = d - u_j \quad \text{or} \quad C_j = d + v_j .
--   $$
--
--   This is Property III(G) of Baker and Scudder: with tolerances, some job incurs no penalty and sits exactly at the boundary of its window. It reduces the search for an optimal due date to the $2n$ candidates $C_j - v_j$, $C_j + u_j$, and it is the first step towards Property IV(G), which identifies which job and which end.
--
--   **Formalization Note** "In an optimal schedule" is read for a fixed sequence, with $d$ the least optimal due date for that sequence; if a sequence and due date are jointly optimal with $d$ least among such optima, then $d$ is the least optimal due date of that sequence, so this reading implies the paper's. The statement is not made for every optimal $d$, which is false on a flat stretch of $f$; the least one is the paper's choice (p. 34). Existence is part of the conclusion, so the statement is not vacuous; $n \ge 1$ is needed for it, since $f \equiv 0$ when $n = 0$.
-- source:
--   Baker and Scudder, Sequencing with earliness and tardiness penalties: a review, Oper. Res. 38 (1990), p. 30, Property III(G); restated and proved p. 34 (Appendix)

import Mathlib
import Definitions.Def_BakerScudder1990_Tolerance_Instance

namespace BakerScudder1990.Tolerance

open Instance

/-- Property III(G) (Baker and Scudder 1990, p. 30; proof p. 34). For a fixed sequence of
`n > 0` jobs processed without inserted idle time, a least optimal common due date exists, and at
every least optimal due date `d` some job `k` completes at an end of its tolerance window:
`C_k = d - u_k` or `C_k = d + v_k`. -/
theorem property_III_G {n : ℕ} (I : Instance n) (hn : 0 < n) :
    (∃ d : ℝ, I.IsLeastOptimalDueDate d) ∧
      ∀ d : ℝ, I.IsLeastOptimalDueDate d →
        ∃ k : Fin n, I.C k = d - I.u k ∨ I.C k = d + I.v k := by sorry

end BakerScudder1990.Tolerance
