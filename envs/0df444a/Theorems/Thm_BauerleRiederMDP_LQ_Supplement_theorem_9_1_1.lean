-- Prove2me | Theorems.Thm_BauerleRiederMDP_LQ_Supplement_theorem_9_1_1
-- name    : BauerleRiederMDP.LQ.Supplement.theorem_9_1_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-27T00:03:22.219024+00:00
-- url     : https://prove2.me/theorems/28465375-f777-4520-bfb0-b596bca60eef
-- title:
--   Theorem 9.1.1 — consumption-investment with random horizon: structure, unique fixed point, optimal strategy, policy iteration
-- statement:
--   For the consumption-investment problem with random horizon and $\beta  p \alpha _b < 1$ it holds: a) $J_\infty $ is increasing, concave and continuous; b) $J_\infty  = \lim _{n\to \infty } J_n$ and $J_\infty $ is the unique fixed point of $T$ in $IB_b$; c) there exists a maximizer $f^*$ of $J_\infty $, and the stationary strategy $(f^*, f^*, \dots )$ is optimal for the consumption-investment problem with random horizon; d) the policy iteration holds.
--
--   **Formalization Note.** `M = C.mdp` is the stationary model of §9.1 with discount $\beta p$; $J_\infty $, $J_n$, $T$, $IB_b$ (with $b(x) = 1 + x$), $D^*_n$, $Ls$ are the published `MDPFinance.Contracting` objects; $\alpha _b = \max {1, v_0}$. $J_\infty $ is shown real-valued and its real version $Jr$ is increasing, concave (over $[0, \infty )$) and continuous. Optimality in c) is for problem (9.1) itself: the stationary strategy $c_n = f^*_c(X_n)$, $\varphi _n = f^*_a(X_n)$ is admissible and its objective equals the supremum `C.value x` over all admissible strategies, for every initial wealth $x \ge  0$. "The policy iteration holds" is Theorem 7.3.6 c), d): $\emptyset  \ne  Ls D^*_n(x) \subset  D^*_\infty (x)$ for all $x$, and some $f^* \in  F$ with $f^*(x) \in  Ls D^*_n(x)$ gives an optimal stationary policy. Uniqueness of the fixed point is in all of $IB_b$.
--
--   Differences from the source:
--   - encoding: 𝔼_x[∑_{n<τ} β^n U_c(c_n) + β^τ U_p(X_τ)] with τ geometric and independent → ∑_n β^n p^n 𝔼U_c(c_n) + ∑_n β^{n+1}(1−p)p^n 𝔼U_p(X_{n+1}); reason: Fubini with the independent τ, all terms nonnegative; same value
--   - encoding: (F_n)-adapted strategies, X_τ ∈ dom U_p a.s. → measurable functions of (R_1,…,R_n), X_n ≥ 0 a.s. for every n ≥ 1; reason: F_n = F^S_n and ℙ(τ = n) > 0 for every n; same class
--   - reading: "the policy iteration holds" → Theorem 7.3.6 c), d); reason: the book's reference for the policy iteration
-- source:
--   Bäuerle & Rieder, Markov Decision Processes with Applications to Finance (2011), Theorem 9.1.1, p.269 (PDF 279)

import Mathlib
import Definitions.Def_MDPFinance_Contracting_Model
import Definitions.Def_MDPFinance_Contracting_Value
import Definitions.Def_MDPFinance_Contracting_Bounding
import Definitions.Def_MDPFinance_Contracting_LsSet
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_mdp
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_wealth
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_IsStrategy
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_objective
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_value
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_v0
import Definitions.Def_BauerleRiederMDP_LQ_Supplement_CIRandom_markovWealth

open MeasureTheory ProbabilityTheory Filter Topology
open MDPFinance.Contracting
open scoped NNReal ENNReal

namespace BauerleRiederMDP.LQ.Supplement

/-- **Theorem 9.1.1** (Bäuerle & Rieder, *Markov Decision Processes with Applications to Finance*
(2011), Theorem 9.1.1, p.269, PDF 279, model of §9.1, pp.267–269, PDF 277–279). For the
consumption-investment problem with random horizon and `β p α_b < 1` it holds:
a) `J_∞` is increasing, concave and continuous;
b) `J_∞ = lim_{n→∞} J_n` and `J_∞` is the unique fixed point of `T` in `IB_b`;
c) there exists a maximizer `f*` of `J_∞`, and the stationary strategy `(f*, f*, …)` is optimal for
the consumption-investment problem with random horizon;
d) the policy iteration holds.

**Formalization Note.** `M = C.mdp` is the stationary model of §9.1 with discount `βp`; `J_∞`,
`J_n`, `T`, `IB_b` (with `b(x) = 1 + x`), `D*_n`, `Ls` are the published `MDPFinance.Contracting`
objects; `α_b = max{1, v_0}`. `J_∞` is shown real-valued and its real version `Jr` is increasing,
concave (over `[0, ∞)`) and continuous. Optimality in c) is for problem (9.1) itself: the stationary
strategy `c_n = f*_c(X_n)`, `φ_n = f*_a(X_n)` is admissible and its objective equals the supremum
`C.value x` over all admissible strategies, for every initial wealth `x ≥ 0`. "The policy iteration
holds" is Theorem 7.3.6 c), d): `∅ ≠ Ls D*_n(x) ⊂ D*_∞(x)` for all `x`, and some `f* ∈ F` with
`f*(x) ∈ Ls D*_n(x)` gives an optimal stationary policy. Uniqueness of the fixed point is in all
of `IB_b`. -/
theorem theorem_9_1_1 {d : ℕ} (C : CIRandom d)
    (hcontr : ENNReal.ofReal (C.β * C.p) * max 1 C.v0 < 1) :
    let M := C.mdp
    let Jr : ℝ≥0 → ℝ := fun x => (Jinf M x).toReal
    let b : ℝ≥0 → ℝ := fun x => 1 + (x : ℝ)
    let stratC : (ℝ≥0 → ℝ × (Fin d → ℝ)) → ℝ → (n : ℕ) → (Fin n → Fin d → ℝ) → ℝ :=
      fun f x n r => (f (CIRandom.markovWealth f x n r).toNNReal).1
    let stratφ : (ℝ≥0 → ℝ × (Fin d → ℝ)) → ℝ → (n : ℕ) → (Fin n → Fin d → ℝ) → Fin d → ℝ :=
      fun f x n r => (f (CIRandom.markovWealth f x n r).toNNReal).2
    -- a)
    ((∀ x, Jinf M x = ((Jr x : ℝ) : EReal)) ∧ Monotone Jr ∧ ConcaveOn ℝ≥0 Set.univ Jr ∧
      Continuous Jr) ∧
    -- b)
    ((∀ x, Tendsto (fun n => Jn M M.r n x) atTop (𝓝 (Jinf M x))) ∧ Jr ∈ IBb b ∧
      T M (Jinf M) = Jinf M ∧
      ∀ v ∈ IBb b, T M (fun y => (v y : EReal)) = (fun y => (v y : EReal)) → v = Jr) ∧
    -- c)
    (∃ fstar : ℝ≥0 → ℝ × (Fin d → ℝ), IsMaximizerOf M (Jinf M) fstar ∧
      ∀ x : ℝ, 0 ≤ x → C.IsStrategy x (stratC fstar x) (stratφ fstar x) ∧
        C.objective x (stratC fstar x) (stratφ fstar x) = C.value x) ∧
    -- d) policy iteration (Theorem 7.3.6 c), d))
    ((∀ x, (LsSeq (fun n => Dstar M (Jn M M.r n) x)).Nonempty ∧
        LsSeq (fun n => Dstar M (Jn M M.r n) x) ⊆ Dstar M (Jinf M) x) ∧
      ∃ fstar : ℝ≥0 → ℝ × (Fin d → ℝ), IsDecisionRuleOf M fstar ∧
        (∀ x, fstar x ∈ LsSeq (fun n => Dstar M (Jn M M.r n) x)) ∧
        ∀ x, Jinfpi M M.r (fun _ => fstar) x = Jinf M x) := by sorry

end BauerleRiederMDP.LQ.Supplement
