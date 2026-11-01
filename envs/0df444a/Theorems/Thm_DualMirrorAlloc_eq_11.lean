-- Prove2me | Theorems.Thm_DualMirrorAlloc_eq_11
-- name    : DualMirrorAlloc.eq_11
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:16.400708+00:00
-- url     : https://prove2.me/theorems/44081b40-0570-4f2f-8dae-a54c8230df36
-- title:
--   Proof of Theorem 1, Step 2, (11), pp.15–16 — mirror-descent regret on $w_t(\mu)=\mu^\top(\rho-b_t(x_t))$ up to $\tau_A$
-- statement:
--   Throughout, the requests satisfy the model of §2 (p.8) and Assumption 1 with constants $\bar f,\bar b\ge0$; the reference function $h$ satisfies Assumption 2 with $\sigma>0$; $\eta>0$; $\mu_1\in\mathbb R^m_+$ is a point where $h$ is differentiable within $\mathbb R^m_+$; and $\tilde x_t$, $\mu_{t+1}$ are produced by arbitrary argmax and mirror-step selections.
--
--   Let $w_t(\mu)=\mu^\top(\rho-b_t(x_t))$ and $E(t,\mu)=\frac1{2\sigma}(\bar b+\bar\rho)^2\eta\,t+\frac1\eta V_h(\mu,\mu_1)$. For every request sequence $\vec\gamma$ and every $\mu\in\mathbb R^m_+$,
--   $$
--   \sum_{t=1}^{\tau_A}\big(w_t(\mu_t)-w_t(\mu)\big)\le E(\tau_A,\mu)\le E(T,\mu).
--   $$
--
--   Both inequalities are asserted. This bounds the complementary-slackness term of (10) against any pivot $\mu$.
--
--   **Formalization Note** Periods are 0-based (sums over indices $t<\tau_A$). The statement is pathwise.
--
--   Differences from the source:
--   - reading: σ-strongly convex reference function; resources j ∈ [m] → 0 < σ and 0 < m; reason: C₂ and E(t, µ) divide by σ, and ρ̲ = min_j ρ_j > 0 (p.14) needs m ≥ 1
--   - encoding: step-size η ≥ 0 → 0 < η; reason: at η = 0 the mirror step (4) and the term C₃/η are undefined
--   - encoding: requests γ = (f, b, X) ∈ S → a type S of requests carrying X s, f s, b s (structure Requests); f s, b s typed on all of ℝ^d; reason: values of f, b off X_s are never used
--   - encoding: ‖b(x)‖∞ ≤ b̄ with b(x) ≥ 0; ‖·‖₁ → ∀ j, b_s(x)_j ≤ b̄; ℓ₁ norm as Σ_j |v_j|; reason: Mathlib's norm on Fin m → ℝ is the sup norm; the explicit forms are the paper's norms
--   - encoding: x̃_t ∈ arg max (3) and µ_{t+1} = arg min (4) → arbitrary selections act and md with the maximizer / minimizer property (every selection is covered); reason: the paper's arg max / arg min is a choice among optimal solutions
--   - reading: Assumption 1.4: the optimization problems in (3) admit an optimal solution → act s µ maximizes f_s(x) − µᵀb_s(x) over X_s for every request s and every µ ∈ ℝ^m_+; reason: (3) is posed at the dual iterate µ_t, which can be any point of ℝ^m_+
--   - encoding: ∇h in V_h and in Assumption 2.2 → fderivWithin ℝ h ℝ^m_+ (the derivative within the orthant); 2.2 required at points µ₂ where it exists; µ₁ a point where h is differentiable within ℝ^m_+; md's property required at such points; reason: ∇h exists only at differentiability points; on the orthant the derivative within it is unique and equals the gradient wherever h is differentiable
--   - reading: Assumption 2.1: h is differentiable or essentially smooth (Bauschke et al., 2001) in ℝ^m_+ → DifferentiableOn ℝ h ℝ^m_+ (one-sided at the boundary) ∨ IsEssentiallySmoothOrthant h (differentiable on the open orthant, ‖∇h‖ → ∞ at every boundary point); reason: both branches kept; the cited notion with domain ℝ^m_+; the one-sided reading of differentiability is the weaker hypothesis
--   - encoding: periods t = 1, …, T (sums Σ_{t=1}^{τ}, iterates µ_t) → periods Fin T, 0-based: sums over indices t < τ, and the state at index t is (µ_{t+1}, B_{t+1}); reason: index convention only
--   - reading: τ_A: the first time less than T at which some resource has Σ_{t=1}^{τ_A}(b_t(x_t))_j + b̄ ≥ ρ_jT, else T → the least t ∈ {0, …, T − 1} with that property (sum over the first t periods, empty at t = 0), else T; reason: with the search starting at t = 1 the Step-1 claim fails: m = T = 1, ρ = 1, b̄ = 2, a request with b(x̃₁) = 2 gives x₁ = 0 ≠ x̃₁ while τ_A = 1
-- source:
--   Balseiro–Lu–Mirrokni, The Best of Many Worlds: Dual Mirror Descent for Online Allocation Problems, arXiv:2011.10124v3, proof of Theorem 1, Step 2, (11), pp.15–16

import Mathlib
import Definitions.Def_DualMirrorAlloc_Bregman
import Definitions.Def_DualMirrorAlloc_Model

namespace DualMirrorAlloc

/-- **Display (11): mirror-descent regret on the complementary-slackness functions.**
Balseiro–Lu–Mirrokni, arXiv:2011.10124v3, proof of Theorem 1, Step 2, (11), pp.15–16: "we obtain
from Proposition 5 that for every µ ∈ Rm+
Σ_{t=1}^{τA} wt(µt) − wt(µ) ≤ E(τA, µ) ≤ E(T, µ), where E(t, µ) = (1/2σ)(b̄ + ρ̄)²η·t +
(1/η)Vh(µ, µ1)".

For every request sequence `γ⃗` and every `µ ∈ ℝ^m_+`, both inequalities, with
`w_t(µ) = µᵀ(ρ − b_t(x_t))`.

**Formalization Note.** Time is 0-based: `Σ_{t=1}^{τ_A}` is the sum over indices `t < τ_A`, and
`dualIter … t` is `µ_{t+1}`. Pathwise, under the standing hypotheses of Theorem 1 without the
measurability hypotheses. -/
theorem eq_11 {S : Type*} {d m : ℕ} (hm : 0 < m)
    (R : Requests S d m) (ρ : Fin m → ℝ) (hmodel : IsModel R ρ)
    (fbar bbar : ℝ) (hA1 : Assumption1 R fbar bbar)
    (h : (Fin m → ℝ) → ℝ) (σ : ℝ) (hσ : 0 < σ) (hA2 : Assumption2 h σ)
    (η : ℝ) (hη : 0 < η)
    (mu₁ : Fin m → ℝ) (hmu₁ : mu₁ ∈ orthant m)
    (hmu₁d : DifferentiableWithinAt ℝ h (orthant m) mu₁)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (hact : IsArgmaxSelection R act)
    (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ)) (hmd : IsMirrorStep h η md)
    (T : ℕ) (γ : Fin T → S) (mu : Fin m → ℝ) (hmu : mu ∈ orthant m) :
    (∑ t : Fin T with t.val < tauA R ρ act md mu₁ bbar γ,
        (wFn R ρ act md mu₁ γ t (dualIter R ρ act md mu₁ γ t) - wFn R ρ act md mu₁ γ t mu)) ≤
        errTerm h ρ bbar σ η mu₁ (tauA R ρ act md mu₁ bbar γ) mu ∧
      errTerm h ρ bbar σ η mu₁ (tauA R ρ act md mu₁ bbar γ) mu ≤
        errTerm h ρ bbar σ η mu₁ T mu := by sorry

end DualMirrorAlloc
