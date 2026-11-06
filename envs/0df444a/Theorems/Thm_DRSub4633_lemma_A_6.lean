-- Prove2me | Theorems.Thm_DRSub4633_lemma_A_6
-- name    : DRSub4633.lemma_A_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:05:10.631438+00:00
-- url     : https://prove2.me/theorems/600876a0-e81a-4fe2-9b3f-c3373f2ea0ba
-- title:
--   Lemma A.6 — constant-profile bounds
-- statement:
--   Let $q_0=157/200$ and $q\in[1/2,1]$.
--
--   1. If $q\ge q_0$, then $F_q$ changes sign exactly once on $[0,1]$, from negative to positive. Consequently, for $0\le\tau\le T\le 1$, $\int_\tau^TF_q\le\max\{0,\int_\tau^1F_q\}$.
--   2. If $q\le q_0$, then $F_q\le 7/80$ on $[0,1]$.
--   3. If $t_0\le\tau\le 1$, then $\int_\tau^1F_q\le\int_\tau^1F_1=I(\tau)$.
--   4. If $t_1\le t\le 1$, then $F_q(t)\le F_1(t)$ and $F_1(t)>0$.
--
--   Differences from the source:
--   - reading: F_q changes sign exactly once on [0,1], from negative to positive → there is c ∈ (0,1) with F_q < 0 on [0, c) and F_q > 0 on (c, 1]; reason: the precise meaning of a single sign change from negative to positive; both signs occur and no other change happens
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma A.6, p.50

import Mathlib
import Definitions.Def_DRSub4633_FqInt
import Definitions.Def_DRSub4633_Itail
import Definitions.Def_DRSub4633_t0
import Definitions.Def_DRSub4633_t1

namespace DRSub4633

/-- **Lemma A.6 (Constant-profile bounds).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma A.6, p.50, with `q₀ = 157/200`: "Let
`q ∈ [1/2, 1]`. (i) If `q ≥ q₀`, then `F_q` changes sign exactly once on `[0, 1]`, from negative to
positive. Consequently, for `0 ≤ τ ≤ T ≤ 1`, `∫_τ^T F_q ≤ max{0, ∫_τ^1 F_q}`. (ii) If `q ≤ q₀`, then
`F_q ≤ 7/80` on `[0, 1]`. (iii) If `t₀ ≤ τ ≤ 1`, then `∫_τ^1 F_q ≤ ∫_τ^1 F_1 = I(τ)`, with `I` as in
(127). (iv) If `t₁ ≤ t ≤ 1`, then `F_q(t) ≤ F_1(t)` and `F_1(t) > 0`."

**Formalization Note.** "Changes sign exactly once on `[0, 1]`, from negative to positive" is: there
is `c ∈ (0, 1)` with `F_q < 0` on `[0, c)` and `F_q > 0` on `(c, 1]` (both signs occur, and no other
sign change). -/
theorem lemma_A_6 (q : ℝ) (hq : q ∈ Set.Icc (1 / 2 : ℝ) 1) :
    (157 / 200 ≤ q →
      (∃ c ∈ Set.Ioo (0 : ℝ) 1, (∀ t ∈ Set.Ico (0 : ℝ) c, FqInt q t < 0) ∧
        (∀ t ∈ Set.Ioc c 1, 0 < FqInt q t)) ∧
      (∀ τ T : ℝ, 0 ≤ τ → τ ≤ T → T ≤ 1 →
        ∫ t in τ..T, FqInt q t ≤ max 0 (∫ t in τ..1, FqInt q t))) ∧
    (q ≤ 157 / 200 → ∀ t ∈ Set.Icc (0 : ℝ) 1, FqInt q t ≤ 7 / 80) ∧
    (∀ τ ∈ Set.Icc t0 1,
      ∫ t in τ..1, FqInt q t ≤ ∫ t in τ..1, FqInt 1 t ∧ ∫ t in τ..1, FqInt 1 t = Itail τ) ∧
    (∀ t ∈ Set.Icc t1 1, FqInt q t ≤ FqInt 1 t ∧ 0 < FqInt 1 t) := by sorry

end DRSub4633
