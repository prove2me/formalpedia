-- Prove2me | Theorems.Thm_Apery_classCount_eq
-- name    : Apery.classCount_eq
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T21:00:35.439846+00:00
-- url     : https://prove2.me/theorems/36f86983-7c28-4f4b-9e1f-6a656e308eb5
-- title:
--   Per-class counts of the entry roots: $\mathrm{classCount} = b_a + (2\text{ or }1)(\nu_s(a)+\nu_t(a))$
-- statement:
--   **Per-class counts of the entry roots (4.4).** For $p = 2m+1$, dimensions $L$, basis indices $s, t$ and a residue class $c \bmod p$, the number $\mathrm{classCount}\,p\,K\,(\mathrm{entryRoots}\,N\,L\,s\,t)\,c$ of roots of $D_N^6 E_s E_t$ in the class $c$, corrected by the poles, equals $b_{a} + (2 \text{ if } a = 0 \text{ else } 1)(\nu_s(a) + \nu_t(a))$ with $a = \mathrm{ccls}(c)$ and $b_a = \mathrm{Bse}\,p\,K\,N\,a$. This is `classCount_eq` of `Apery/Arith/ClassCount.lean` (with the auxiliary `card_filter_replicate`, `count_classRoots`, `count_DN`, `card_plc_PlK`, `ccls_eq_zero_iff`); it converts the per-class entry inequalities into the closed form used by `Apery.inner_bound_cap`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/ClassCount.lean#L196-L230

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

theorem classCount_eq {p m : ℕ} [hp : Fact p.Prime] (hm : 2 * m + 1 = p) (K N : ℕ)
    (L : Fin (m + 1) → ℕ) (s t : Σ a : Fin (m + 1), Fin (L a)) (c : ZMod p) :
    classCount p K (entryRoots N L s t) c =
      Bse p K N (ccls hm c) + (if ccls hm c = 0 then 2 else 1) *
        ((nu L s (ccls hm c) : ℚ) + nu L t (ccls hm c)) := by
  sorry

end Apery
