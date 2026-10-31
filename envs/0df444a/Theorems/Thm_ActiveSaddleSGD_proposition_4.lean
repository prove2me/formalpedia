-- Prove2me | Theorems.Thm_ActiveSaddleSGD_proposition_4
-- name    : ActiveSaddleSGD.proposition_4
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T04:11:13.015981+00:00
-- url     : https://prove2.me/theorems/6db4088d-19a6-49f4-85e2-8fe4ca94810d
-- title:
--   Proposition 4 — the projected iterates are a Robbins–Monro recursion (corrected: $D$ extends $\nabla(F\circ P_M)$ from the ball of radius $2r$)
-- statement:
--   Let Assumptions 1, 2 and 4 hold. Then $(y_n^N)_{n\ge N}$ satisfies
--   $$
--   y_{n+1}^N=y_n^N-\gamma_nD(y_n^N)+\gamma_n\tilde\eta_{n+1}^N+\gamma_n\varrho_{n+1}^N+\gamma_n\tilde\varrho_{n+1}^N,
--   $$
--   where $(\tilde\eta_n^N)$ is given by (16) and $(\varrho_n^N)$, $(\tilde\varrho_n^N)$ are such that all three are adapted, and there is $C>0$ such that for all $n\ge N$:
--
--   1. $\|\varrho_{n+1}^N\|\le C\gamma_n(1+\|\eta_{n+1}\|^2)\mathbb 1_{\tau_N>n+1}$;
--   2. $\|\tilde\varrho_{n+1}^N\|\le C\|z_n^N\|(1+\|\eta_{n+1}\|)$;
--   3. $\mathbb E_n\tilde\eta_{n+1}^N=0$ and $\mathbb E_n\|\tilde\eta_{n+1}^N\|^4<C$.
--
--   Moreover:
--
--   4. $E^-\subset T_{x^*}M$ and $E^-\subset E_D^-$, the eigenspace of $J_D(x^*)$ for its negative eigenvalues;
--   5. on the event $[y_n^N\to x^*]$,
--   $$
--   \liminf_n\mathbb E_n\|P_{E_D^-}\tilde\eta_{n+1}^N\|\ge\liminf_n\mathbb E_n\|P_{E^-}\tilde\eta_{n+1}^N\|>0.
--   $$
--
--   The projected iterates thus satisfy almost all assumptions of Proposition 3; what remains is the rate at which $z_n^N$ vanishes.
--
--   **Formalization Note** The recursion and clauses 1, 2 hold for every $\omega$; clause 3 and clause 5 hold almost surely. As in the source, $C$ may depend on $N$.
--
--   Differences from the source:
--   - correction: $D$ is a bounded continuous extension of $\nabla(F\circ P_M)$ from $B(0,r)$ → $D$ agrees with $\nabla(F\circ P_M)$ on the closed ball of radius $2r$; reason: if $M$ is curved, a point $x$ with $\|x\|\le r$ can have $\|P_M(x)\|>r$; take $D$ continuous with $\|D(y)-\nabla(F\circ P_M)(y)\|\asymp\mathrm{dist}(y,B(0,r))^{1/2}$ outside the ball; at such $y=y_n^N$ the printed bounds, of size $\|z_n^N\|+\gamma_n$, cannot absorb that error, while $P_M(B(0,r))\subset B(0,2r)$ because $0\in M$
--   - encoding: $N\ge0$ → $N\ge1$; reason: $\gamma_{N-1}$ is undefined at $N=0$ and the events $\mathcal A_N$ increase, so nothing is lost
--   - encoding: "$r$ fixed, adjusted in the course of the proof" → $\exists r_1>0,\ \forall r\in(0,r_1)$; reason: that is what p.18 and "for $r$ small enough" say
--   - encoding: the proofs set $x^*=0$ → general $x^*$, with balls around $x^*$; reason: translation; same instances
--   - encoding: $P_M$ on a ball → a total map $P$ with `IsProjectionOn`; reason: only its values on the ball are constrained; same instances
--   - encoding: $n<\tau_N$ → "stayed in the ball from $N$ to $n$" (`StayedIn`); reason: no value in $\mathbb N\cup\{\infty\}$ is needed; same event
--   - reading: "Almost surely, … there is $A,B>0$" in Assumption 4 → deterministic $A,B>0$, chosen before "almost surely"; reason: Proposition 4 iii) and Lemma 4 give a deterministic $C$, which a random bound $B$ would not, and the proof of Lemma 4 (p.21) bounds $\mathbb E_n\|\eta_{n+1}\|^4$ by a constant
-- source:
--   Bianchi, Hachem & Schechtman, Stochastic Subgradient Descent Escapes Active Strict Saddles on Weakly Convex Functions, arXiv:2108.02072v4, Proposition 4, p.19, with (16), p.20

import Mathlib
import Definitions.Def_PathoSubgrad_Circle_Setting
import Definitions.Def_ProjLikeRetr_Retractor_tangentBundle
import Definitions.Def_ActiveSaddleSGD_ManifoldCalculus
import Definitions.Def_ActiveSaddleSGD_ActiveManifold
import Definitions.Def_ActiveSaddleSGD_Algorithm
import Definitions.Def_ActiveSaddleSGD_Noise
import Definitions.Def_ActiveSaddleSGD_ProjectedIterates

open ProjLikeRetr.Retractor MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace ActiveSaddleSGD

/-- Bianchi, Hachem & Schechtman, arXiv:2108.02072v4, Proposition 4, p.19 (with (16), p.20): under
Assumptions 1, 2 and 4, `(y_n^N)_{n≥N}` satisfies
`y_{n+1}^N = y_n^N − γ_n D(y_n^N) + γ_n η̃_{n+1}^N + γ_n ϱ_{n+1}^N + γ_n ϱ̃_{n+1}^N` with adapted
sequences, and there is `C > 0` such that for all `n ≥ N`:
i) `‖ϱ_{n+1}^N‖ ≤ C γ_n (1 + ‖η_{n+1}‖²) 𝟙_{τ_N>n+1}`; ii) `‖ϱ̃_{n+1}^N‖ ≤ C ‖z_n^N‖ (1 + ‖η_{n+1}‖)`;
iii) `E_n η̃_{n+1}^N = 0` and `E_n‖η̃_{n+1}^N‖⁴ < C`. Moreover iv) `E⁻ ⊆ T_{x*}M` and `E⁻ ⊆ E_D⁻`, and
v) on `[y_n^N → x*]`, `liminf E_n‖P_{E_D⁻} η̃_{n+1}^N‖ ≥ liminf E_n‖P_{E⁻} η̃_{n+1}^N‖ > 0`.

**Formalization Note** "`r` fixed with `0 < r < r₁`" (p.18) is `∃ r₁ > 0, ∀ r ∈ (0, r₁)`; `D` is any field
of `IsProjectedField`, that is an extension from the ball of radius `2r`; `N ≥ 1` (see `projIter`).
As on the page, `C` comes after `N`. `η̃` is the `noiseTilde` of (16). i), ii) and the recursion hold
for every `ω`, and iii) almost surely. `x*` is general where the page has `0`. -/
theorem proposition_4 {d k : ℕ} {f F : EuclideanSpace ℝ (Fin d) → ℝ}
    {G : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)}
    {M U : Set (EuclideanSpace ℝ (Fin d))} {xs w : EuclideanSpace ℝ (Fin d)} {Cv β : ℝ}
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ℱ : Filtration ℕ mΩ} {x v η : ℕ → Ω → EuclideanSpace ℝ (Fin d)} {γ : ℕ → ℝ} {c₁ c₂ α : ℝ}
    (hA1 : Assumption1 f ℱ x v η γ c₁ c₂ α)
    (hA2 : Assumption2 k f F G M U xs w Cv β)
    (hA4 : Assumption4 μ ℱ η (negEigenspace (curvOp M G xs)))
    (P : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)) (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hP : IsProjectionOn M P xs r₀) :
    ∃ r₁ > 0, ∀ r, 0 < r → r < r₁ →
      ∀ D : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d), IsProjectedField F P D xs r →
      ∀ N : ℕ, 1 ≤ N →
      ∃ ρ ρt : ℕ → Ω → EuclideanSpace ℝ (Fin d),
        (∀ n, N ≤ n →
          StronglyMeasurable[ℱ n] (noiseTilde x η xs P (projIter x η γ xs P D r N) r N n) ∧
          StronglyMeasurable[ℱ n] (ρ n) ∧ StronglyMeasurable[ℱ n] (ρt n)) ∧
        (∀ n, N ≤ n → ∀ ω,
          projIter x η γ xs P D r N (n + 1) ω =
            projIter x η γ xs P D r N n ω - γ n • D (projIter x η γ xs P D r N n ω)
              + γ n • noiseTilde x η xs P (projIter x η γ xs P D r N) r N (n + 1) ω
              + γ n • ρ (n + 1) ω + γ n • ρt (n + 1) ω) ∧
        (∃ C > 0, ∀ n, N ≤ n →
          (∀ ω, ‖ρ (n + 1) ω‖ ≤
            Set.indicator {a | StayedIn x xs r N (n + 1) a}
              (fun a => C * γ n * (1 + ‖η (n + 1) a‖ ^ 2)) ω) ∧
          (∀ ω, ‖ρt (n + 1) ω‖ ≤
            C * ‖projResidual x xs P r N n ω‖ * (1 + ‖η (n + 1) ω‖)) ∧
          (∀ᵐ ω ∂μ,
            (μ[noiseTilde x η xs P (projIter x η γ xs P D r N) r N (n + 1) | ℱ n]) ω = 0 ∧
            condLExp (ℱ n) μ (fun a =>
              ‖noiseTilde x η xs P (projIter x η γ xs P D r N) r N (n + 1) a‖ₑ ^ 4) ω <
                ENNReal.ofReal C)) ∧
        (negEigenspace (curvOp M G xs) ≤ tangentSpace M xs ∧
          negEigenspace (curvOp M G xs) ≤ negEigenspace (fderiv ℝ D xs)) ∧
        (∀ᵐ ω ∂μ, Tendsto (fun n => projIter x η γ xs P D r N n ω) atTop (𝓝 xs) →
          liminf (fun n => condLExp (ℱ n) μ (fun a =>
              ‖(negEigenspace (curvOp M G xs)).starProjection
                (noiseTilde x η xs P (projIter x η γ xs P D r N) r N (n + 1) a)‖ₑ) ω) atTop ≤
            liminf (fun n => condLExp (ℱ n) μ (fun a =>
              ‖(negEigenspace (fderiv ℝ D xs)).starProjection
                (noiseTilde x η xs P (projIter x η γ xs P D r N) r N (n + 1) a)‖ₑ) ω) atTop ∧
          0 < liminf (fun n => condLExp (ℱ n) μ (fun a =>
              ‖(negEigenspace (curvOp M G xs)).starProjection
                (noiseTilde x η xs P (projIter x η γ xs P D r N) r N (n + 1) a)‖ₑ) ω) atTop) := by sorry

end ActiveSaddleSGD
