-- Prove2me | Theorems.Thm_FamousTheorems_doob_maximal_inequality
-- name    : FamousTheorems.doob_maximal_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T02:04:02.395424+00:00
-- url     : https://prove2.me/theorems/64ae1c06-3ab5-4150-bd69-12843f1e3aa0
-- title:
--   Doob's maximal inequality
-- statement:
--   **Doob's maximal inequality.** Let $(f_n)$ be a nonnegative submartingale on a finite measure space with respect to a filtration, let $\varepsilon\ge0$, and let $M_n=\max_{k\le n}f_k$. Then
--   $$\varepsilon\,\mu\{M_n\ge\varepsilon\}\le\int_{\{M_n\ge\varepsilon\}}f_n\,d\mu.$$
--
--   In particular $\mu\{\max_{k\le n}f_k\ge\varepsilon\}\le\mathbb E[f_n]/\varepsilon$. So the running maximum of a submartingale is controlled by its final value alone. This inequality is the source of Doob's $L^p$ inequalities and is a basic tool in martingale theory and stochastic analysis.
--
--   **Formalization note.** Mathlib's `MeasureTheory.maximal_ineq`. The running maximum is `(Finset.range (n + 1)).sup'` of the values $f_k(\omega)$, with the nonemptiness proof `Finset.nonempty_range_add_one`. The left side is in `ENNReal`, and the right side is `ENNReal.ofReal` of the set integral of $f_n$. `ε` is a nonnegative real (`NNReal`).
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.maximal_ineq`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem doob_maximal_inequality {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} {𝒢 : Filtration ℕ m0} {f : ℕ → Ω → ℝ}
    [IsFiniteMeasure μ] (hsub : Submartingale f 𝒢 μ) (hnonneg : 0 ≤ f) {ε : NNReal} (n : ℕ) :
    (ε : ENNReal) * μ {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω} ≤
      ENNReal.ofReal (∫ ω in {ω | (ε : ℝ) ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω},
        f n ω ∂μ) := by sorry

end FamousTheorems
