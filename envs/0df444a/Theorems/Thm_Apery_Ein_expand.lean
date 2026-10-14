-- Prove2me | Theorems.Thm_Apery_Ein_expand
-- name    : Apery.Ein_expand
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T17:09:37.738902+00:00
-- url     : https://prove2.me/theorems/102c35d2-88fc-4d96-ad15-6416a3a79d36
-- title:
--   Expansion of the inner profile: $E_{\mathrm{in}}(x,k)$ on a window in $(\lfloor x\rfloor, \lfloor\alpha x\rfloor, \lfloor 2\lambda x\rfloor)$
-- statement:
--   On every window $q \le x < q+1$, $q' \le \tfrac{3}{40}x < q'+1$, $\mu \le 2\cdot\tfrac{37}{40}x < \mu+1$ (with $x \le 400$), the continuous inner profile expands as
--
--   $$E_{\mathrm{in}}(x,k) = -2\lambda x\,q + 12\lambda x\,q' + \Bigl(2\mu\lambda x - \frac{\mu(\mu+1)}{2}\Bigr) - \lambda x\,k + 2\sum_{i,j} b_{ij}(q,q',k)\,c_{ij}(x-q,\ \alpha x - q'),$$
--
--   $\lambda = 37/40$, $\alpha = 3/40$. This is `Ein_expand` of `Apery/Growth/TableGen.lean`; the proof file also contains the outer expansion `Eout_expand` and the helpers `nat_floor_of_bounds`, `fract_of_bounds`, `two_Jc_eq`, `two_Jc_lin`, `psiR_eq`, `toNat_cast_q`. **Formalization Note** `Ein`, `bIn`, `ccount`, `Jc` are the platform definitions.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/TableGen.lean#L107-L116

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

lemma Ein_expand {x : ℝ} (k : ℤ) {q q' μ : ℕ} (hq1 : (q : ℝ) ≤ x) (hq2 : x < q + 1)
    (hr1 : (q' : ℝ) ≤ 3 / 40 * x) (hr2 : 3 / 40 * x < q' + 1)
    (hm1 : (μ : ℝ) ≤ 2 * (37 / 40 * x)) (hm2 : 2 * (37 / 40 * x) < μ + 1) (hx : x ≤ 400) :
    Ein x k = -2 * (37 / 40 * x) * q + 12 * (37 / 40 * x) * q' +
      (2 * μ * (37 / 40 * x) - (μ : ℝ) * (μ + 1) / 2) - 37 / 40 * x * k +
      2 * ∑ i, ∑ j, bIn q q' k i j * ccount (x - q) (3 / 40 * x - q') i j := by
  sorry

end Apery
