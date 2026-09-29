-- Prove2me | Theorems.Thm_FoundationsML_MaxEnt_maxent_l1_generalization_bound
-- name    : FoundationsML.MaxEnt.maxent_l1_generalization_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-20T04:17:59.011983+00:00
-- url     : https://prove2.me/theorems/ed7f0525-400f-429b-a5ab-fbea99f750bd
-- title:
--   Theorem 12.3 — Maxent L1-regularization generalization bound (milestone)
-- statement:
--   **Statement (Theorem 12.3, p. 303, PDF p. 320).** Fix $\delta>0$. Let $\hat w$ be a solution
--   of the optimization (12.12) for $\lambda=2R_m(H)+r\sqrt{\log(2/\delta)/(2m)}$. Then, with
--   probability at least $1-\delta$ over the draw of an i.i.d. sample $S$ of size $m$ from $D$,
--   $$L_D(\hat w) \le \inf_w\big[L_D(w) + 2\|w\|_1\lambda\big].$$
--   The infimum's scope covers the whole bracketed sum, with the regularization penalty tied to
--   the *same* bound variable $w$ the infimum ranges over — not to $\hat w$'s own norm — matching
--   the book's own proof (p. 320), which derives $L_D(\hat w) - L_D(w) \le 2\lambda\|w\|_1$ for
--   *every* comparator $w$.
--
--   This is the chapter's generalization guarantee for the L1-regularized Maxent dual solution:
--   it bounds the population log-loss of the empirical dual optimizer $\hat w$ in terms of the
--   best achievable population log-loss, plus a complexity-driven regularization penalty
--   identical in form to chunk `04`'s SRM bound and built from the same Rademacher-complexity
--   machinery (Eq. 12.5) that motivates the whole Maxent principle in the first place.
-- source:
--   Mohri, Rostamizadeh & Talwalkar, Foundations of Machine Learning, 2nd ed., MIT Press 2018, p. 303, Theorem 12.3 (PDF p. 320)

import Mathlib
import Definitions.Def_FoundationsML_MaxEnt_LogLoss
import Definitions.Def_FoundationsML_MaxEnt_EmpiricalLogLoss
import Definitions.Def_FoundationsML_MaxEnt_RademacherComplexity

open MeasureTheory

namespace FoundationsML.MaxEnt

/-- Theorem 12.3 (Mohri, Rostamizadeh & Talwalkar, *Foundations of Machine Learning*, 2nd ed.,
MIT Press 2018, p. 303, PDF p. 320). Fix `δ > 0`. Let `ŵ` be a solution of the optimization
(12.12) for `λ = 2R_m(H) + r·sqrt(log(2/δ)/(2m))`. Then, with probability at least `1 − δ` over
the draw of an i.i.d. sample `S` of size `m` from `D`,
`L_D(ŵ) ≤ inf_w[L_D(w) + 2‖w‖_1·λ]`.

**Formalization Note.** "`ŵ` is a solution of the optimization (12.12)" — `inf_w λ‖w‖_1 −
(1/m)∑_i log p_w(x_i)`, whose objective is `λ‖w‖_1 + L_S(w)` (`EmpiricalLogLoss`) — is
expressed as the hypothesis `∀ w, λ‖ŵ‖_1 + L_S(ŵ) ≤ λ‖w‖_1 + L_S(w)` inside the probability
event, universally quantified over every `ŵ` satisfying it (the standard Lean idiom for "let
`ŵ` be *a* minimizer," matching that (12.12)'s minimizer need not be unique). `H` is the
feature-function family of §12.2 (containing every component `Φ_j`), matching the book's use of
`R_m(H)` (not `R_m(Φ)` or a per-coordinate complexity).

**Revision (2026-09-19).** The conclusion's `⨅` now binds the sum of the loss and the penalty,
both in terms of the same bound variable `w`: `L_D(ŵ) ≤ ⨅ w, [L_D(w) + 2‖w‖_1·λ]`. The book's
own proof (p. 320) derives, for *any* comparator `w`, `L_D(ŵ) − L_D(w) ≤ 2λ‖w‖_1`, i.e.
`L_D(ŵ) ≤ L_D(w) + 2λ‖w‖_1` for every `w`, hence `L_D(ŵ) ≤ inf_w[L_D(w) + 2λ‖w‖_1]` — the
infimum's scope covers the whole bracketed sum, with the norm term tied to the *same* `w` the
infimum ranges over. The previously drafted `(⨅ w, L_D(w)) + 2‖ŵ‖_1·λ` charged the penalty
against the *minimizer's own* norm and covered only `L_D(w)` with the infimum — a different,
unproven quantity (neither dominates the other in general) — and matches neither the proof nor
Theorem 12.5's structurally identical `inf_w[L_D(w) + λ‖w‖_2²]` form. -/
theorem maxent_l1_generalization_bound
    {X : Type*} [Fintype X] [MeasurableSpace X] [MeasurableSingletonClass X]
    {N : ℕ} (p0 : X → ℝ) (hp0 : ∀ x, 0 < p0 x)
    (Φ : X → Fin N → ℝ) (r : ℝ) (hr : 0 ≤ r) (hΦ : ∀ x j, |Φ x j| ≤ r)
    (H : Set (X → ℝ)) (hHΦ : ∀ j : Fin N, (fun x => Φ x j) ∈ H)
    (D : Measure X) [IsProbabilityMeasure D]
    (m : ℕ) (hm : 0 < m) (δ : ℝ) (hδ : 0 < δ) :
    let lam := 2 * RademacherComplexity D H m + r * Real.sqrt (Real.log (2 / δ) / (2 * m))
    (1 - δ) ≤ (Measure.pi (fun _ : Fin m => D)
      {S : Fin m → X | ∀ ŵ : Fin N → ℝ,
        (∀ w : Fin N → ℝ,
            lam * (∑ j, |ŵ j|) + EmpiricalLogLoss p0 Φ S ŵ ≤
              lam * (∑ j, |w j|) + EmpiricalLogLoss p0 Φ S w) →
        LogLoss p0 Φ D ŵ ≤
          ⨅ w : Fin N → ℝ, (LogLoss p0 Φ D w + 2 * (∑ j, |w j|) * lam)}).toReal := by sorry

end FoundationsML.MaxEnt
