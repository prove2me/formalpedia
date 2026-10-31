-- Prove2me | Theorems.Thm_ActiveSaddleSGD_proposition_3
-- name    : ActiveSaddleSGD.proposition_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:12:12.723829+00:00
-- url     : https://prove2.me/theorems/c5690bb9-e429-4a45-8a3b-4af5bce06f03
-- title:
--   Proposition 3 — avoidance of traps with the perturbation $\tilde\varrho$
-- statement:
--   Let $D:\mathbb R^d\to\mathbb R^d$ be $C^3$ near $0$ with $D(0)=0$ and $J_D(0)=P\,\mathrm{diag}(J^+,J^-)\,P^{-1}$, where the eigenvalues of $J^+$ have nonnegative real parts, those of $J^-$ negative real parts, and $d^-\ge1$. Let $(\gamma_n)$ be deterministic and nonnegative with $\sum\gamma_i=+\infty$, $\sum\gamma_i^2<+\infty$. Let
--   $$
--   y_{n+1}=y_n-\gamma_nD(y_n)+\gamma_n\tilde\eta_{n+1}+\gamma_n\varrho_{n+1}+\gamma_n\tilde\varrho_{n+1},
--   $$
--   with $(\tilde\eta_n)$, $(\varrho_n)$, $(\tilde\varrho_n)$ adapted and $\|\tilde\eta_n\|$, $\|\tilde\varrho_n\|$ with finite fourth moments. Write $(\tilde\eta_n^+,\tilde\eta_n^-)=P^{-1}\tilde\eta_n$. Let $\Gamma$ be an event such that almost surely on $[y_n\to0]\cap\Gamma$:
--
--   1. $\mathbb E_n\tilde\eta_{n+1}=0$ for all $n$;
--   2. $\limsup\mathbb E_n\|\tilde\eta_{n+1}\|^4<+\infty$;
--   3. $\liminf\mathbb E_n\|\tilde\eta_{n+1}^-\|>0$;
--   4. $\sum_i\|\varrho_{i+1}\|^2<+\infty$;
--   5. $\limsup\mathbb E_n\|\tilde\varrho_{n+1}\|^4<+\infty$;
--   6. $\lim\mathbb E_n\|\tilde\varrho_{n+1}\|^2=0$;
--   7. $\limsup\chi_n^{-1/2}\sum_{i\ge n}\gamma_i\mathbb E_n\|\tilde\varrho_{i+1}\|=0$.
--
--   Then
--   $$
--   \mathbb P(\Gamma\cap[y_n\to0])=0.
--   $$
--
--   This is a nonconvergence theorem for stochastic approximation which allows the perturbation $\tilde\varrho$ that the projection onto $M$ creates, and which is not square summable.
--
--   **Formalization Note** $P$ is a linear equivalence $\mathbb R^{d^+}\times\mathbb R^{d^-}\to\mathbb R^d$. Conditional moments are `condLExp`; the sums are in $[0,\infty]$.
--
--   Differences from the source:
--   - generalization: $P$ with the Jordan blocks of $J_D(0)$ → any invertible $P$ with $J_D(0)=P\,\mathrm{diag}(J^+,J^-)P^{-1}$; reason: the proof uses only the signs of the real parts; the Jordan factorization is an instance
--   - reading: "stochastic process $(y_n)$" with $y_0$ $\mathcal F_0$-measurable → $(y_n)$ strongly adapted; reason: the page calls $(w_n^-)$ adapted and does not state that $D$ is measurable; in the application $D$ is continuous
--   - encoding: the identification $\mathbb R^d=\mathbb R^{d^+}\oplus\mathbb R^{d^-}$ → a continuous linear equivalence from the product; reason: it fixes $d=d^++d^-$; same instances
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Proposition 3, p.17, with the set-up of p.16

import Mathlib
import Definitions.Def_ActiveSaddleSGD_ProjectedIterates
import Definitions.Def_ActiveSaddleSGD_CenterStable
import Definitions.Def_ActiveSaddleSGD_Repulsive

open MeasureTheory Filter Topology
open scoped ENNReal

universe u

namespace ActiveSaddleSGD

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Proposition 3, p.17 (with the set-up of p.16):
let `D : ℝᵈ → ℝᵈ` be `C³` near `0`, `D(0) = 0`, with `J_D(0) = P diag(J⁺, J⁻) P⁻¹`, `d⁻ ≥ 1`. If
`y_{n+1} = y_n − γ_n D(y_n) + γ_n η̃_{n+1} + γ_n ϱ_{n+1} + γ_n ϱ̃_{n+1}` with adapted sequences and `η̃`, `ϱ̃` in
`L⁴`, and if clauses i)–vii) hold almost surely on `[y_n → 0] ∩ Γ`, then `ℙ(Γ ∩ [y_n → 0]) = 0`.

**Formalization Note** `P` is a linear equivalence `ℝ^{d⁺} × ℝ^{d⁻} ≃ ℝᵈ`, which fixes `d = d⁺ + d⁻`.
`P⁻¹η̃_n = (η̃_n⁺, η̃_n⁻)`, and `(·).2` is the `d⁻` block. `P` need not give Jordan blocks. `(y_n)` is
assumed adapted ("stochastic process", p.17), which contains `y₀` being `𝓕₀`-measurable. Conditional
moments are `condLExp`, sums are in `ℝ≥0∞`. -/
theorem proposition_3 {d dp dm : ℕ} (hdm : 0 < dm)
    (D : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hD : ∃ V ∈ 𝓝 (0 : EuclideanSpace ℝ (Fin d)), ContDiffOn ℝ 3 D V) (hD0 : D 0 = 0)
    (P : (EuclideanSpace ℝ (Fin dp) × EuclideanSpace ℝ (Fin dm)) ≃L[ℝ] EuclideanSpace ℝ (Fin d))
    (Jp : Matrix (Fin dp) (Fin dp) ℝ) (Jm : Matrix (Fin dm) (Fin dm) ℝ)
    (hJp : HasNonnegRealParts Jp) (hJm : HasNegRealParts Jm)
    (hJ : fderiv ℝ D 0 =
      (P : _ →L[ℝ] _) ∘L ((matCLM Jp).prodMap (matCLM Jm)) ∘L (P.symm : _ →L[ℝ] _))
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (ℱ : Filtration ℕ mΩ) (γ : ℕ → ℝ) (hγ : IsStepSequence γ)
    (y ηt ρ ρt : ℕ → Ω → EuclideanSpace ℝ (Fin d))
    (hrec : ∀ n ω, y (n + 1) ω = y n ω - γ n • D (y n ω) + γ n • ηt (n + 1) ω
      + γ n • ρ (n + 1) ω + γ n • ρt (n + 1) ω)
    (hy : StronglyAdapted ℱ y) (hηt : StronglyAdapted ℱ ηt) (hρ : StronglyAdapted ℱ ρ)
    (hρt : StronglyAdapted ℱ ρt)
    (hηt4 : ∀ n, MemLp (ηt n) 4 μ) (hρt4 : ∀ n, MemLp (ρt n) 4 μ)
    (Γ : Set Ω) (hΓ : MeasurableSet Γ)
    (hyp : ∀ᵐ ω ∂μ, ω ∈ Γ → Tendsto (fun n => y n ω) atTop (𝓝 0) →
      (∀ n, (μ[ηt (n + 1) | ℱ n]) ω = 0) ∧
      limsup (fun n => condLExp (ℱ n) μ (fun a => ‖ηt (n + 1) a‖ₑ ^ 4) ω) atTop < ⊤ ∧
      0 < liminf (fun n => condLExp (ℱ n) μ (fun a => ‖(P.symm (ηt (n + 1) a)).2‖ₑ) ω) atTop ∧
      ∑' i, ‖ρ (i + 1) ω‖ₑ ^ 2 < ⊤ ∧
      limsup (fun n => condLExp (ℱ n) μ (fun a => ‖ρt (n + 1) a‖ₑ ^ 4) ω) atTop < ⊤ ∧
      Tendsto (fun n => condLExp (ℱ n) μ (fun a => ‖ρt (n + 1) a‖ₑ ^ 2) ω) atTop (𝓝 0) ∧
      limsup (fun n => ENNReal.ofReal (tailChi γ n ^ (-(1 / 2) : ℝ)) *
        ∑' i, ENNReal.ofReal (γ (n + i)) *
          condLExp (ℱ n) μ (fun a => ‖ρt (n + i + 1) a‖ₑ) ω) atTop = 0) :
    μ (Γ ∩ {ω | Tendsto (fun n => y n ω) atTop (𝓝 0)}) = 0 := by sorry

end ActiveSaddleSGD
