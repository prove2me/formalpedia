-- Prove2me | Theorems.Thm_DualMirrorAlloc_eq_10
-- name    : DualMirrorAlloc.eq_10
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:30.226232+00:00
-- url     : https://prove2.me/theorems/11b84222-8c0c-4189-b1cd-9ce499d617a6
-- title:
--   Proof of Theorem 1, Step 1, (10), p.15 — expected reward before $\tau_A$ via the expected dual objective
-- statement:
--   Throughout, the requests satisfy the model of §2 (p.8) and Assumption 1 with constants $\bar f,\bar b\ge0$; the reference function $h$ satisfies Assumption 2 with $\sigma>0$; $\eta>0$; $\mu_1\in\mathbb R^m_+$ is a point where $h$ is differentiable within $\mathbb R^m_+$; and $\tilde x_t$, $\mu_{t+1}$ are produced by arbitrary argmax and mirror-step selections. In addition the selections are measurable as in Theorem 1. Let $P$ be any probability law on $S$ and $\vec\gamma\sim P^T$ (i.i.d. requests). With $\bar D(\mu|P)=\mathbb E_{s\sim P}[f^*_s(\mu)]+\rho^\top\mu$ and $\bar\mu_{\tau}=\frac1\tau\sum_{t=1}^{\tau}\mu_t$,
--   $$
--   \mathbb E\Big[\sum_{t=1}^{\tau_A}f_t(x_t)\Big]=\mathbb E\Big[\sum_{t=1}^{\tau_A}\bar D(\mu_t|P)\Big]-\mathbb E\Big[\sum_{t=1}^{\tau_A}\mu_t^\top(\rho-b_t(x_t))\Big]
--   \ \ge\ \mathbb E\big[\tau_A\bar D(\bar\mu_{\tau_A}|P)\big]-\mathbb E\Big[\sum_{t=1}^{\tau_A}\mu_t^\top(\rho-b_t(x_t))\Big].
--   $$
--
--   Both the equality and the inequality are asserted. The display is the primal half of the proof: it lower-bounds the algorithm's reward up to the stopping time by the expected dual objective at the average dual iterate, minus a complementary-slackness term.
--
--   **Formalization Note** Expectations are Bochner integrals under `Measure.pi (fun _ : Fin T => P)`. $\bar\mu_0$ is $0$; it is multiplied by $\tau_A=0$.
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
--   - reading: expectations of OPT(γ⃗) and of the run, τ_A 'a random variable' (pp.9, 14–15), no measurability conditions stated → S has a σ-algebra; (s, µ) ↦ f_s(act s µ) and (s, µ) ↦ b_s(act s µ) measurable, s ↦ f_s(0) measurable, (g, µ) ↦ md g µ measurable; reason: the smallest conditions under which every expectation in the proof is a genuine expectation; Lean's integral of a non-measurable function is 0
--   - encoding: μ̄_{τ_A} = (1/τ_A)Σ_{t=1}^{τ_A} µ_t, undefined at τ_A = 0 → the value 0 at τ_A = 0; reason: it appears only multiplied by τ_A = 0
--   - reading: D̄(µ|P) = E_{(f,b)∼P}[f*(µ_t)] + µ_tᵀρ (p.15) → D̄(µ|P) = ∫ f*_s(µ) dP(s) + ρᵀµ; reason: the left side is a function of µ; µ_t is a misprint for µ
--   - encoding: i.i.d. requests from P ∈ Δ(S) → an arbitrary probability measure P on S, γ⃗ ∼ Measure.pi (fun _ : Fin T => P), T ≥ 1; reason: the product measure is the law of T i.i.d. draws
-- source:
--   Balseiro–Lu–Mirrokni, The Best of Many Worlds: Dual Mirror Descent for Online Allocation Problems, arXiv:2011.10124v3, proof of Theorem 1, Step 1, (10), p.15

import Mathlib
import Definitions.Def_DualMirrorAlloc_Bregman
import Definitions.Def_DualMirrorAlloc_Model

open MeasureTheory

namespace DualMirrorAlloc

/-- **Display (10): the reward before `τ_A` in terms of the dual objective.** Balseiro–Lu–Mirrokni,
arXiv:2011.10124v3, proof of Theorem 1, Step 1, (10), p.15: "summing (9) from t = 1, …, τA we
obtain that
E[Σ_{t=1}^{τA} ft(xt)] = E[Σ_{t=1}^{τA} D̄(µt|P)] − E[Σ_{t=1}^{τA} µtᵀ(ρ − bt(xt))]
≥ E[τA D̄(µ̄τA|P)] − E[Σ_{t=1}^{τA} µtᵀ(ρ − bt(xt))]".

Both clauses, under the hypotheses of Theorem 1 and for every law `P` of the requests, with all
expectations over `γ⃗ ∼ P^T`.

**Formalization Note.** Time is 0-based: `Σ_{t=1}^{τ_A}` is the sum over indices `t < τ_A`, and
`dualIter … t` is `µ_{t+1}`. `µ̄_{τ_A}` is `dualAvg … (τ_A)` (value `0` at `τ_A = 0`, where it is
multiplied by `0`). `OPT` plays no role here, so its measurability is not assumed. -/
theorem eq_10 {S : Type*} [MeasurableSpace S] {d m : ℕ} (hm : 0 < m)
    (R : Requests S d m) (ρ : Fin m → ℝ) (hmodel : IsModel R ρ)
    (fbar bbar : ℝ) (hA1 : Assumption1 R fbar bbar)
    (h : (Fin m → ℝ) → ℝ) (σ : ℝ) (hσ : 0 < σ) (hA2 : Assumption2 h σ)
    (η : ℝ) (hη : 0 < η)
    (mu₁ : Fin m → ℝ) (hmu₁ : mu₁ ∈ orthant m)
    (hmu₁d : DifferentiableWithinAt ℝ h (orthant m) mu₁)
    (act : S → (Fin m → ℝ) → (Fin d → ℝ)) (hact : IsArgmaxSelection R act)
    (md : (Fin m → ℝ) → (Fin m → ℝ) → (Fin m → ℝ)) (hmd : IsMirrorStep h η md)
    (hf_act : Measurable (fun p : S × (Fin m → ℝ) => R.f p.1 (act p.1 p.2)))
    (hb_act : Measurable (fun p : S × (Fin m → ℝ) => R.b p.1 (act p.1 p.2)))
    (hf_zero : Measurable (fun s => R.f s 0))
    (hmd_meas : Measurable (Function.uncurry md))
    (T : ℕ) (hT : 1 ≤ T) (P : Measure S) [IsProbabilityMeasure P] :
    (∫ γ, (∑ t : Fin T with t.val < tauA R ρ act md mu₁ bbar γ,
        R.f (γ t) (played R ρ act md mu₁ γ t)) ∂(Measure.pi fun _ : Fin T => P) =
      (∫ γ, (∑ t : Fin T with t.val < tauA R ρ act md mu₁ bbar γ,
          dualBar R ρ P (dualIter R ρ act md mu₁ γ t)) ∂(Measure.pi fun _ : Fin T => P)) -
        ∫ γ, (∑ t : Fin T with t.val < tauA R ρ act md mu₁ bbar γ,
          dualIter R ρ act md mu₁ γ t ⬝ᵥ (ρ - R.b (γ t) (played R ρ act md mu₁ γ t)))
          ∂(Measure.pi fun _ : Fin T => P)) ∧
    (∫ γ, ((tauA R ρ act md mu₁ bbar γ : ℝ) *
          dualBar R ρ P (dualAvg R ρ act md mu₁ γ (tauA R ρ act md mu₁ bbar γ)))
          ∂(Measure.pi fun _ : Fin T => P)) -
        (∫ γ, (∑ t : Fin T with t.val < tauA R ρ act md mu₁ bbar γ,
          dualIter R ρ act md mu₁ γ t ⬝ᵥ (ρ - R.b (γ t) (played R ρ act md mu₁ γ t)))
          ∂(Measure.pi fun _ : Fin T => P)) ≤
      (∫ γ, (∑ t : Fin T with t.val < tauA R ρ act md mu₁ bbar γ,
          dualBar R ρ P (dualIter R ρ act md mu₁ γ t)) ∂(Measure.pi fun _ : Fin T => P)) -
        ∫ γ, (∑ t : Fin T with t.val < tauA R ρ act md mu₁ bbar γ,
          dualIter R ρ act md mu₁ γ t ⬝ᵥ (ρ - R.b (γ t) (played R ρ act md mu₁ γ t)))
          ∂(Measure.pi fun _ : Fin T => P) := by sorry

end DualMirrorAlloc
