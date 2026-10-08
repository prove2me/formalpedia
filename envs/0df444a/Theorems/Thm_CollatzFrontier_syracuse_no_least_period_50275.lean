-- Prove2me | Theorems.Thm_CollatzFrontier_syracuse_no_least_period_50275
-- name    : CollatzFrontier.syracuse_no_least_period_50275
-- status  : Proved
-- author  : @Xiang Huang
-- created : 2026-10-04T17:36:28.943165+00:00
-- url     : https://prove2.me/theorems/efb1f864-5ba7-4dbe-a76f-951cb11fddc8
-- title:
--   No Syracuse cycle has least period 50275
-- statement:
--   No positive integer $m$ has Syracuse orbit with **least** period exactly $50275$: there is no $m>0$ with $T^{50275}(m)=m$ and $T^k(m)\ne m$ for every $0<k<50275$.
--
--   This follows by combining the companion theorem `syracuse_least_cycle_distinct_budget` with the already-**Proved** platform baseline [`syracuse_no_cycle_below_2310000`](https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875), which forces every state of such a hypothetical cycle to be at least $2310000$ (using that $T(1)=1$ is the unique small periodic point); the resulting distinct-state envelope is then shown to fail by an explicit arithmetic certificate.
--
--   This theorem is unconditional on the Prove2Me platform: it relies only on the already-Proved baseline above, imported by name, not re-proved or assumed as an axiom. It excludes only the single isolated least period $50275$. It does **not** raise the global minimal-period lower bound of $6291$ established by [`syracuse_period_le_6290_eq_one`](https://prove2.me/theorems/f0416d07-cb79-4120-a2dc-e83cc8fbcdd5) (equivalently, the open tail starts at [`syracuse_minimal_period_ge_6291_eq_one`](https://prove2.me/theorems/27c2e735-af66-4ff7-af77-9ac4694d59b1)), and it does not address any other period or the Collatz conjecture.
--
--   **Formalization Note.** This is a restatement, without the `baseline` parameter, of the repo's conditional theorem `no_least_cycle_50275_of_certified_baseline`, which takes the finite-baseline proposition as an explicit function argument rather than an axiom. Since that exact proposition is the proved platform theorem cited above, the published statement here drops the parameter and the solution supplies the proved theorem directly, making the result unconditional given platform content.
-- source:
--   Original contribution of this submission, adapting the private repository collatz-frontier, commit 4d656b9c9c5815305bd391f206c9d3e9587dd395 (branch main), file lean/CollatzFrontier/Cycle50275.lean, declaration CollatzFrontier.no_least_cycle_50275_of_certified_baseline (restated here without the baseline parameter, which is discharged in the solution by the already-Proved platform theorem syracuse_no_cycle_below_2310000, https://prove2.me/theorems/73735589-bbad-479f-8d7e-375fd2f82875). The arithmetic certificate route follows a product-free sixth-power telescoping certificate (one recorded check: ~2 s vs ~29 s for the 50275-term product) from the private research branch research/rotated-word-budget-20261002 @ b50c78f40ebd2aa9a55eeeff431f75b84eeed74c, files lean/CollatzFrontier/TelescopingCycleBudget.lean and lean/CollatzFrontier/SixthPower50275.lean, in place of the 50275-term balanced-product certificate in lean/CollatzFrontier/Cycle50275Arithmetic.lean. Does not raise the global lower bound established by syracuse_period_le_6290_eq_one, https://prove2.me/theorems/f0416d07-cb79-4120-a2dc-e83cc8fbcdd5 (open tail syracuse_minimal_period_ge_6291_eq_one, https://prove2.me/theorems/27c2e735-af66-4ff7-af77-9ac4694d59b1).

import Mathlib
import Definitions.Def_syracuseStep

namespace CollatzFrontier

theorem syracuse_no_least_period_50275 (m : ℕ) (hm : 0 < m)
    (hcyc : syracuseStep^[50275] m = m)
    (hmin : ∀ k : ℕ, 0 < k → k < 50275 → syracuseStep^[k] m ≠ m) : False := by sorry

end CollatzFrontier
