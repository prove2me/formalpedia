-- Prove2me | Theorems.Thm_Apery_outer_frame
-- name    : Apery.outer_frame
-- status  : Proved
-- author  : @tomasz
-- created : 2026-10-12T21:36:57.461459+00:00
-- url     : https://prove2.me/theorems/19cb57b3-c1e0-4d5e-a5dc-884ea86752fa
-- title:
--   The outer-range framework: $v_p^G(\Delta) \ge 2\sum w - r$
-- statement:
--   **The outer-range framework.** Let $p \ge 5$, and let $E_s$ ($s < 37n$) be integer polynomials of degree $< 37n$ whose reductions mod $p$ split as $\prod_{c \ne cls(s)} (X - \gamma_c)^{L_c} (X - \gamma_{cls(s)})^{idx(s)}$ with $\gamma$ injective and $(cls, idx)$ injective on $\{(cls(s), idx(s))\}$; let weights $w \le 0$ satisfy the per-entry bound $v_p^G\big(\mu_X(D_{3n}^6 E_s E_t) - \mu_{\ge}(D_{3n}^6 E_s E_t / D_{40n})\big) \ge w_s + w_t$. Then $v_p^G(\Delta_n) \ge 2\sum_s w_s - (37n - (2p + 22n - 3 - (37n - 1)))$, the rank-$r$ correction being the number of moments of degree $\ge 2p-3$. This is `outer_frame` of `Apery/Arith/OuterFrame.lean`: `\mu = \mu_{<} + \mu_{\ge}`, the low-rank factorisation of the $\mu_{\ge}$-part and the low-rank determinant lemma `det_lowrank_bound` of `Apery/Arith/LowRank.lean`. It is the framework consumed by `Apery.outer_bound`.
-- source:
--   https://github.com/mo271/Zeta5/blob/7fe736760f4b96bfdb4334b68e3b3124ecbe10b0/Apery/Arith/OuterFrame.lean#L96-L215

import Mathlib
import Definitions.Def_Zeta5_SourceConstruction
import Definitions.Def_Zeta5_SourceArith
import Definitions.Def_Zeta5_SourceGrowthTables
import Definitions.Def_Zeta5_SourceInner
import Definitions.Def_Zeta5_SourceOuter
import Definitions.Def_Zeta5_SourcePoleFun
import Definitions.Def_Zeta5_SourcePullback
import Definitions.Def_Zeta5_SourceValToolkit

open Finset Polynomial Matrix

namespace Apery

theorem outer_frame {p : ℕ} [hp : Fact p.Prime] (hp5 : 5 ≤ p) (n : ℕ) (Ez : Fin (37 * n) → ℤ[X])
    (hdegZ : ∀ s, (Ez s).natDegree < 37 * n) {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ : ι → ZMod p) (hγ : Function.Injective γ) (Lc : ι → ℕ) (cls : Fin (37 * n) → ι)
    (idx : Fin (37 * n) → ℕ) (hidx : ∀ a, idx a < Lc (cls a))
    (hinj : ∀ a b, cls a = cls b → idx a = idx b → a = b)
    (hred : ∀ a, (Ez a).map (Int.castRingHom (ZMod p)) =
      (∏ c ∈ Finset.univ.erase (cls a), (X - C (γ c)) ^ Lc c) * (X - C (γ (cls a))) ^ idx a)
    (w : Fin (37 * n) → ℚ) (hw : ∀ s, w s ≤ 0)
    (hA : ∀ s t, GV p (μX (40 * n) (D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) *
        (Ez t).map (Int.castRingHom ℚ)) -
      C (μGe p ((D (3 * n) ^ 6 * (Ez s).map (Int.castRingHom ℚ) *
        (Ez t).map (Int.castRingHom ℚ)) /ₘ D (40 * n)))) (w s + w t)) :
    GV p (Δ n) (2 * ∑ s, w s - ((37 * n - ((2 * p + 22 * n - 3) - (37 * n - 1)) : ℕ) : ℚ)) := by
  sorry

end Apery
