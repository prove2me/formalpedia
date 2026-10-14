-- Prove2me | Theorems.Thm_Apery_class_frame
-- name    : Apery.class_frame
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T21:13:38.891987+00:00
-- url     : https://prove2.me/theorems/2009e215-01fa-4bb6-ab6d-cba3e6ddd18b
-- title:
--   The class-basis framework: entry bounds $\Rightarrow v_p^G(\Delta n) \ge 2\sum_s w_s$
-- statement:
--   **The class-basis framework (4.3).** Let $p = 2m+1 \ge 5$, dimensions $L_a$ with $\sum_a L_a = 37n$, weights $w$ on the basis indices $E_{a,i}$ of $E_{a,i} = \prod_{c \neq a} (t + c^2)^{L_c} (t + a^2)^i$, and suppose every entry inequality $w_s + w_t + 4 \le \mathrm{classCount}\,p\,(40n)\,(\mathrm{entryRoots}\,(3n)\,L\,s\,t)\,c$ holds for all classes $c$. Then the Hankel-type determinant satisfies $v_p^G(\Delta n) \ge 2\sum_s w_s$. This is `class_frame` of `Apery/Arith/ClassFrame.lean`: the per-class entry bounds on $\mu_X(tpol\,M/D_K)$ (`Apery.muX_tpol_bound`) and the unimodularity of the class bases (`Apery.coeffMat_det_unit`) combine through `det_basis_change` and the pullback to give the determinant bound. It is the framework consumed by `Apery.inner_bound_cap`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/ClassFrame.lean#L97-L168 (+ ClassCount.lean sq_injective)

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceInner
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial

namespace Apery

theorem class_frame {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) {m : ℕ} (hm : 2 * m + 1 = p)
    (n : ℕ) (L : Fin (m + 1) → ℕ) (hL : ∑ c, L c = 37 * n)
    (w : (Σ a : Fin (m + 1), Fin (L a)) → ℚ)
    (hsep : Sep p (PlK (40 * n))) (hK : 40 * n < p ^ 2)
    (hdeg : 5 + 2 * (18 * n + 2 * (37 * n)) - 2 * (40 * n) + 1 < p ^ 2)
    (hentry : ∀ s t : (Σ a : Fin (m + 1), Fin (L a)), ∀ c : ZMod p,
      w s + w t + 4 ≤ classCount p (40 * n) (entryRoots (3 * n) L s t) c) :
    GV p (Δ n) (2 * ∑ s, w s) := by
  sorry

end Apery
