-- Prove2me | Theorems.Thm_Apery_Eout_expand
-- name    : Apery.Eout_expand
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T16:08:59.679099+00:00
-- url     : https://prove2.me/theorems/84571533-19d5-4cc0-801c-e315baa3f433
-- title:
--   Expansion of the outer profile: $E_{\mathrm{out}}(x)$ on a window in $(\lfloor x\rfloor, \lfloor\alpha x\rfloor, \lfloor 2\lambda x\rfloor)$
-- statement:
--   On every window $q \le x < q+1$, $q' \le \tfrac{3}{40}x < q'+1$, $\mu \le 2\cdot\tfrac{37}{40}x < \mu+1$ (with $x \le 400$), the continuous outer profile expands as
--
--   $$E_{\mathrm{out}}(x) = -2\lambda x\,q + \Bigl(2\mu\lambda x - \frac{\mu(\mu+1)}{2}\Bigr) - 2\sum_{i,j} G_{ij}(q)\,c_{ij}(x-q,\ \alpha x - q') + \max\Bigl(0, \frac{13}{10}x - 2\Bigr),$$
--
--   $\lambda = 37/40$, $\alpha = 3/40$, where $G_{ij}$ are the class-function coefficients and $c_{ij}$ the nine continuous interval counts. This is `Eout_expand` of `Apery/Growth/TableGen.lean`; the file also contains the inner expansion `Ein_expand`, the closed form $2J(u) = 2u^2 - u + \{2u\}(1-\{2u\})/2$ (`two_Jc_lin`), the identity `psiR_eq` and the count lemmas `cc00`..`cc22`. **Formalization Note** The definitions `Eout`, `bGO`, `ccount`, `Jc` are the platform ones.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Growth/TableGen.lean#L118-L125

import Mathlib
import Definitions.Def_Zeta5_SourceGrowthTables

open Finset

namespace Apery

lemma Eout_expand {x : ℝ} {q q' μ : ℕ} (hq1 : (q : ℝ) ≤ x) (hq2 : x < q + 1)
    (hr1 : (q' : ℝ) ≤ 3 / 40 * x) (hr2 : 3 / 40 * x < q' + 1)
    (hm1 : (μ : ℝ) ≤ 2 * (37 / 40 * x)) (hm2 : 2 * (37 / 40 * x) < μ + 1) (hx : x ≤ 400) :
    Eout x = -2 * (37 / 40 * x) * q + (2 * μ * (37 / 40 * x) - (μ : ℝ) * (μ + 1) / 2) -
      2 * ∑ i, ∑ j, bGO q i j * ccount (x - q) (3 / 40 * x - q') i j + max 0 (13 / 10 * x - 2) := by
  sorry

end Apery
