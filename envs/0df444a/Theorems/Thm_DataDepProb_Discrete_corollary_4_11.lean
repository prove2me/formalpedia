-- Prove2me | Theorems.Thm_DataDepProb_Discrete_corollary_4_11
-- name    : DataDepProb.Discrete.corollary_4_11
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T18:10:34.000736+00:00
-- url     : https://prove2.me/theorems/ce15cdf7-3a20-41ac-a1fa-aeadf1da3176
-- title:
--   Corollary 4.11 — penalized KL projection: three-point inequality, exact and with duality gap $\tau$
-- statement:
--   Let $C\subseteq\Delta_d$ be a nonempty closed convex set of positive distributions and $z\in\Delta_d$ have positive coordinates (Fact 4.10). Let $P$ be a continuously differentiable convex function on an open set containing $C$, and $\lambda\ge0$. Define $v=\arg\min_{r\in C}\{\mathrm{KL}(r\|z)+\lambda P(r)\}$. For every $w\in C$,
--   $$\mathrm{KL}(w\|v)+\mathrm{KL}(v\|z)+\lambda P(v)\le\mathrm{KL}(w\|z)+\lambda P(w).$$
--   More generally, for $\tau\ge0$, if $v\in C$ satisfies $\max_{w\in C}\langle\nabla_v(\mathrm{KL}(v\|z)+\lambda P(v)),v-w\rangle\le\tau$, the inequality holds with $\tau$ added to the right-hand side.
--
--   This is the step that makes the penalized projection of §6 compatible with the multiplicative-weights potential.
--
--   Differences from the source:
--   - reading: "define $v=\arg\min$" → the minimizer exists (a conjunct), and the inequality holds for every minimizer; reason: the definition presupposes existence; uniqueness is neither assumed nor needed.
--   - reading: "continuously differentiable convex function on an open set containing $C$" → `ContDiffOn ℝ 1 P U` and `ConvexOn ℝ U P` for an open `U ⊇ C` (`ConvexOn` includes convexity of `U`); reason: convexity of a function presupposes a convex domain.
--   - encoding: $\langle\nabla_v(\cdot),v-w\rangle$ and $\max_{w\in C}\le\tau$ → `fderiv ℝ (fun r => kl r z + lam * P r) v (v - w) ≤ τ` for every `w ∈ C`; reason: the gradient pairing is the Fréchet derivative; a maximum is at most $\tau$ iff every value is.
-- source:
--   Feldman, Kale, Majid, Talwar, Data-Dependent Probability Estimation via Sample Amplification, STOC 2027 submission (manuscript sha256 28400f1c…), p. 10, Corollary 4.11 (with Fact 4.10)

import Mathlib
import Definitions.Def_DataDepProb_Discrete_Simplex
import Definitions.Def_DataDepProb_Discrete_Divergence

namespace DataDepProb.Discrete

/-- Corollary 4.11 (penalized KL projection, p. 10). Let `C ⊆ ∆_d` be a nonempty closed convex
set of positive distributions and `z ∈ ∆_d` have positive coordinates (Fact 4.10); let `P` be
continuously differentiable and convex on an open (convex) set `U ⊇ C`, and `λ ≥ 0`. The
minimizer `v` of `KL(r‖z) + λP(r)` over `C` exists, and for every minimizer `v` and every
`w ∈ C`: `KL(w‖v) + KL(v‖z) + λP(v) ≤ KL(w‖z) + λP(w)`. More generally, for `τ ≥ 0`, if `v ∈ C`
satisfies `max_{w ∈ C} ⟨∇_v(KL(v‖z) + λP(v)), v − w⟩ ≤ τ`, the inequality holds with `τ` added to
the right-hand side. -/
theorem corollary_4_11 {d : ℕ} (C : Set (Fin d → ℝ)) (hCsub : C ⊆ simplex d)
    (hCne : C.Nonempty) (hCcl : IsClosed C) (hCcv : Convex ℝ C) (hCpos : ∀ r ∈ C, ∀ x, 0 < r x)
    (z : Fin d → ℝ) (hz : z ∈ simplex d) (hzpos : ∀ x, 0 < z x)
    (P : (Fin d → ℝ) → ℝ) (U : Set (Fin d → ℝ)) (hU : IsOpen U) (hCU : C ⊆ U)
    (hPd : ContDiffOn ℝ 1 P U) (hPc : ConvexOn ℝ U P) (lam : ℝ) (hlam : 0 ≤ lam) :
    (∃ v ∈ C, IsMinOn (fun r => kl r z + lam * P r) C v) ∧
    (∀ v ∈ C, IsMinOn (fun r => kl r z + lam * P r) C v →
      ∀ w ∈ C, kl w v + kl v z + lam * P v ≤ kl w z + lam * P w) ∧
    ∀ τ : ℝ, 0 ≤ τ → ∀ v ∈ C,
      (∀ w ∈ C, fderiv ℝ (fun r => kl r z + lam * P r) v (v - w) ≤ τ) →
      ∀ w ∈ C, kl w v + kl v z + lam * P v ≤ kl w z + lam * P w + τ := by sorry

end DataDepProb.Discrete
