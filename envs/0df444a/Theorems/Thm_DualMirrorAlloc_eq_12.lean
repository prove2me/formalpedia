-- Prove2me | Theorems.Thm_DualMirrorAlloc_eq_12
-- name    : DualMirrorAlloc.eq_12
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:03:24.159083+00:00
-- url     : https://prove2.me/theorems/e391c967-786b-44e8-82d3-8c9f6f7c42b8
-- title:
--   Proof of Theorem 1, Step 3, (12), p.16 — $\mathbb E[\mathrm{OPT}]\le\tau\bar D(\mu|P)+(T-\tau)\bar f$
-- statement:
--   Assume the model of §2 and Assumption 1 with constants $\bar f,\bar b\ge0$, $m\ge1$, $T\ge1$, and let $P$ be any probability law on $S$. For every real $\tau\in[0,T]$ and every $\mu\in\mathbb R^m_+$,
--   $$
--   \mathbb E_{\vec\gamma\sim P^T}[\mathrm{OPT}(\vec\gamma)]=\frac\tau T\mathbb E_{\vec\gamma\sim P^T}[\mathrm{OPT}(\vec\gamma)]+\frac{T-\tau}T\mathbb E_{\vec\gamma\sim P^T}[\mathrm{OPT}(\vec\gamma)]\le\tau\bar D(\mu|P)+(T-\tau)\bar f .
--   $$
--
--   The page applies it with $\tau=\tau_A$ and $\mu=\bar\mu_{\tau_A}$, sample path by sample path, to compare the benchmark with the dual bound of (10).
--
--   **Formalization Note** $\mathrm{OPT}$ and $s\mapsto f^*_s(\mu)$ are assumed measurable, so the expectations are genuine; both follow from the measurability hypotheses of Theorem 1.
--
--   Differences from the source:
--   - encoding: requests γ = (f, b, X) ∈ S → a type S of requests carrying X s, f s, b s (structure Requests); f s, b s typed on all of ℝ^d; reason: values of f, b off X_s are never used
--   - encoding: ‖b(x)‖∞ ≤ b̄ with b(x) ≥ 0; ‖·‖₁ → ∀ j, b_s(x)_j ≤ b̄; ℓ₁ norm as Σ_j |v_j|; reason: Mathlib's norm on Fin m → ℝ is the sup norm; the explicit forms are the paper's norms
--   - encoding: OPT(γ⃗) = max (1); f*(µ) = sup (2) → real sSup; reason: under the model and Assumption 1 the sets are nonempty and bounded above, so sSup is the supremum (and the maximum when attained)
--   - reading: resources j ∈ [m] → 0 < m; reason: ρ̲ = min_j ρ_j > 0 (p.14) needs m ≥ 1
--   - generalization: the bound at τ_A and the average dual variable µ̄_{τ_A} → every real τ ∈ [0, T] and every µ ∈ ℝ^m_+; reason: the page's 'for any … τ_A ∈ [0, T]' quantifies τ; µ̄_{τ_A} ∈ ℝ^m_+ is an instance of µ
--   - reading: E[OPT(γ⃗)] and D̄(µ|P) taken without stating measurability → γ⃗ ↦ OPT(γ⃗) measurable on S^T, and s ↦ f*_s(µ) measurable for every µ ∈ ℝ^m_+; reason: Lean's integral of a non-measurable function is 0; both are implied by the measurability hypotheses of Theorem 1
--   - encoding: P ∈ Δ(S), γ⃗ ∼ P^T → an arbitrary probability measure P on S and Measure.pi (fun _ : Fin T => P); reason: the product measure is the law of T i.i.d. draws
-- source:
--   Balseiro–Lu–Mirrokni, The Best of Many Worlds: Dual Mirror Descent for Online Allocation Problems, arXiv:2011.10124v3, proof of Theorem 1, Step 3, (12), p.16

import Mathlib
import Definitions.Def_DualMirrorAlloc_Model

open MeasureTheory

namespace DualMirrorAlloc

/-- **Display (12): the benchmark against the expected dual objective.** Balseiro–Lu–Mirrokni,
arXiv:2011.10124v3, proof of Theorem 1, Step 3, (12), p.16: "For any P ∈ Δ(S) and τA ∈ [0, T] we
have that E_{γ⃗∼P^T}[OPT(γ⃗)] = (τA/T) E_{γ⃗∼P^T}[OPT(γ⃗)] + ((T − τA)/T) E_{γ⃗∼P^T}[OPT(γ⃗)] ≤
τA D̄(µ̄τA|P) + (T − τA) f̄, where the inequality uses Proposition 1 and the fact that
OPT(γ⃗) ≤ T f̄."

For every law `P`, every real `τ ∈ [0, T]` and every `µ ∈ ℝ^m_+`, both parts of the display:
`E[OPT] = (τ/T) E[OPT] + ((T − τ)/T) E[OPT] ≤ τ D̄(µ|P) + (T − τ) f̄`, with `E` over `γ⃗ ∼ P^T`.

**Formalization Note.** The page applies the bound at `τ = τ_A` and `µ = µ̄_{τ_A}`; it holds for
every `τ ∈ [0, T]` and every `µ ≥ 0`, which is how it is stated. Measurability of `OPT` and of
`s ↦ f*_s(µ)` makes both expectations genuine (implied by the measurability hypotheses of
Theorem 1). -/
theorem eq_12 {S : Type*} [MeasurableSpace S] {d m : ℕ} (hm : 0 < m)
    (R : Requests S d m) (ρ : Fin m → ℝ) (hmodel : IsModel R ρ)
    (fbar bbar : ℝ) (hA1 : Assumption1 R fbar bbar)
    (T : ℕ) (hT : 1 ≤ T)
    (hOPT : Measurable (fun γ : Fin T → S => OPT R ρ γ))
    (hfstar : ∀ mu ∈ orthant m, Measurable (fun s => fstar R s mu))
    (P : Measure S) [IsProbabilityMeasure P]
    (τ : ℝ) (hτ0 : 0 ≤ τ) (hτT : τ ≤ T) (mu : Fin m → ℝ) (hmu : mu ∈ orthant m) :
    ∫ γ, OPT R ρ γ ∂(Measure.pi fun _ : Fin T => P) =
        τ / T * ∫ γ, OPT R ρ γ ∂(Measure.pi fun _ : Fin T => P) +
          (T - τ) / T * ∫ γ, OPT R ρ γ ∂(Measure.pi fun _ : Fin T => P) ∧
      τ / T * ∫ γ, OPT R ρ γ ∂(Measure.pi fun _ : Fin T => P) +
          (T - τ) / T * ∫ γ, OPT R ρ γ ∂(Measure.pi fun _ : Fin T => P) ≤
        τ * dualBar R ρ P mu + (T - τ) * fbar := by sorry

end DualMirrorAlloc
