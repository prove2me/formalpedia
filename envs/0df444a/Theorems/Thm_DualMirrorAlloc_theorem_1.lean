-- Prove2me | Theorems.Thm_DualMirrorAlloc_theorem_1
-- name    : DualMirrorAlloc.theorem_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:52.618086+00:00
-- url     : https://prove2.me/theorems/3d9181f4-c7f0-4ef0-b71f-0583e672a312
-- title:
--   Theorem 1, (7), p.14 — dual mirror descent has regret $\le C_1+C_2\eta T+C_3/\eta$ under i.i.d. requests
-- statement:
--   Consider the online allocation problem of §2: requests $s\in S$ with feasible sets $X_s\subseteq\mathbb R^d_+$ (compact, $0\in X_s$), rewards $f_s$ and consumptions $b_s$ ($b_s(0)=0$), and a resource vector $\rho$ with $\rho_j>0$, $m\ge1$. Suppose Assumption 1 holds with $\bar f,\bar b\ge0$ ($0\le f\le\bar f$, $b\ge0$, $\|b\|_\infty\le\bar b$ on $X_s$; the maximization problems (3) have optimal solutions) and Assumption 2 holds for the reference function $h$ with modulus $\sigma>0$. Run Algorithm 1 with step size $\eta>0$, initial dual solution $\mu_1\in\mathbb R^m_+$ (a point where $h$ is differentiable within $\mathbb R^m_+$), and any measurable choice of the argmax in (3) and of the minimizer in (4). Then for every $T\ge1$ and every probability law $P$ on $S$, with $\vec\gamma=(\gamma_1,\dots,\gamma_T)$ i.i.d. from $P$,
--   $$
--   \mathbb E_{\vec\gamma\sim P^T}\big[\mathrm{OPT}(\vec\gamma)-R(A|\vec\gamma)\big]\le C_1+C_2\eta T+\frac{C_3}\eta,
--   $$
--   where
--   $$
--   C_1=\frac{\bar f\bar b}{\underline\rho},\qquad C_2=\frac{(\bar b+\bar\rho)^2}{2\sigma},\qquad C_3=\max\big\{V_h(\mu,\mu_1):\mu\in\{0,(\bar f/\rho_1)e_1,\dots,(\bar f/\rho_m)e_m\}\big\},
--   $$
--   $\underline\rho=\min_j\rho_j$, $\bar\rho=\max_j\rho_j$ and $e_j$ the $j$-th unit vector. Since the bound does not depend on $P$, it bounds $\mathrm{Regret}(A)=\sup_{P\in\Delta(S)}\mathbb E_{\vec\gamma\sim P^T}[\mathrm{OPT}(\vec\gamma)-R(A|\vec\gamma)]$.
--
--   With $\eta\asymp T^{-1/2}$ this gives regret $O(\sqrt T)$ for an algorithm that does not know $P$, without convexity of the rewards, consumptions or feasible sets.
--
--   **Formalization Note** The algorithm is fixed before $P$. Measurability is assumed for $(s,\mu)\mapsto f_s(\tilde x(s,\mu))$, $(s,\mu)\mapsto b_s(\tilde x(s,\mu))$, $s\mapsto f_s(0)$, the mirror step, and $\mathrm{OPT}$ on $S^T$; the expectation is the Bochner integral under the product measure.
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
--   - encoding: OPT(γ⃗) = max (1); f*(µ) = sup (2) → real sSup; reason: under the model and Assumption 1 the sets are nonempty and bounded above, so sSup is the supremum (and the maximum when attained)
--   - reading: expectations of OPT(γ⃗) and of the run, τ_A 'a random variable' (pp.9, 14–15), no measurability conditions stated → S has a σ-algebra; (s, µ) ↦ f_s(act s µ) and (s, µ) ↦ b_s(act s µ) measurable, s ↦ f_s(0) measurable, (g, µ) ↦ md g µ measurable; reason: the smallest conditions under which every expectation in the proof is a genuine expectation; Lean's integral of a non-measurable function is 0
--   - reading: E[OPT(γ⃗)] taken without stating measurability → γ⃗ ↦ OPT(γ⃗) measurable on S^T; reason: OPT is a supremum over an uncountable set; Lean's integral of a non-measurable function is 0
--   - encoding: Regret(A) = sup_{P∈Δ(S)} E_{γ⃗∼P^T}[OPT − R] (p.9) → for every probability measure P on S, ∫ (OPT − R) d(Measure.pi (fun _ : Fin T => P)) ≤ bound, with the algorithm and constants fixed before P; reason: a bound for every P is a bound on the supremum; the algorithm does not know P
--   - encoding: ρ̲ = min_j ρ_j, ρ̄ = max_j ρ_j, the max in C₃, (f̄/ρ_j)e_j → ⨅ j, ρ j; ⨆ j, ρ j; max (V_h(0, µ₁)) (⨆ j, V_h((f̄/ρ_j)e_j, µ₁)); Pi.single j (f̄/ρ j); reason: on the finite nonempty index set Fin m these are the min and max
-- source:
--   Balseiro–Lu–Mirrokni, The Best of Many Worlds: Dual Mirror Descent for Online Allocation Problems, arXiv:2011.10124v3, Theorem 1, (7), p.14 (proof pp.14–16)

import Mathlib
import Definitions.Def_DualMirrorAlloc_Bregman
import Definitions.Def_DualMirrorAlloc_Model

open MeasureTheory

namespace DualMirrorAlloc

/-- **Theorem 1 (regret of dual mirror descent under i.i.d. requests).** Balseiro–Lu–Mirrokni,
arXiv:2011.10124v3, Theorem 1, (7), p.14: "Consider Algorithm 1 with step-size η ≥ 0 and initial
solution µ1 ∈ Rm+. Suppose Assumptions 1-2 are satisfied and the requests come from an i.i.d. model
with unknown distribution. Then, it holds for any T ≥ 1 that Regret(A) ≤ C1 + C2ηT + C3/η, where
C1 = f̄b̄/ρ̲, C2 = (b̄ + ρ̄)²/2σ, C3 = max{Vh(µ, µ1) : µ ∈ {0, (f̄/ρ1)e1, …, (f̄/ρm)em}}", with
`Regret(A) = sup_{P∈Δ(S)} E_{γ⃗∼P^T}[OPT(γ⃗) − R(A|γ⃗)]` (p.9).

**Formalization Note.**
- The algorithm (`act`, `md`, `η`, `µ₁`, `h`) and the constants are fixed before the law `P`; the
  bound holds for every probability measure `P` on `S`, which is the bound on the supremum over
  `Δ(S)`. `γ⃗ ∼ P^T` is `Measure.pi (fun _ : Fin T => P)`.
- `η > 0`: at `η = 0` the step (4) and `C₃/η` are undefined.
- The argmax selection `act` and the mirror step `md` are arbitrary selections (every one is
  covered); `µ₁ ∈ ℝ^m_+` is a point where `h` is differentiable within `ℝ^m_+`, so that
  `V_h(·, µ₁)` exists.
- The measurability hypotheses make the expectation a genuine expectation: the reward and the
  consumption of the selected action are jointly measurable in `(s, µ)`, `s ↦ f_s(0)` is
  measurable, the mirror step is measurable in `(g, µ)`, and `OPT` is measurable on `S^T`. -/
theorem theorem_1 {S : Type*} [MeasurableSpace S] {d m : ℕ} (hm : 0 < m)
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
    (T : ℕ) (hT : 1 ≤ T)
    (hOPT : Measurable (fun γ : Fin T → S => OPT R ρ γ)) :
    ∀ (P : Measure S) [IsProbabilityMeasure P],
      ∫ γ, (OPT R ρ γ - reward R ρ act md mu₁ γ) ∂(Measure.pi fun _ : Fin T => P) ≤
        C1 ρ fbar bbar + C2 ρ bbar σ * η * T + C3 h ρ fbar mu₁ / η := by sorry

end DualMirrorAlloc
