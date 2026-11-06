-- Prove2me | Theorems.Thm_DRSub4633_lemma_4_8
-- name    : DRSub4633.lemma_4_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T00:07:10.092605+00:00
-- url     : https://prove2.me/theorems/e8f02642-043a-41dd-adf8-6b6397703ca1
-- title:
--   Lemma 4.8 — ordered integral representation
-- statement:
--   Let $f$ be nonnegative, continuously differentiable and DR-submodular on $Q$, fix $x\in Q$, and let $Y_i$ ($0\le i\le m$), $E=Y_0$, $K_i(t)=Y_i(t)-Y_i(0)-E(t)$ be the paths of (15) and (48). For $0\le i\le m$ the functions
--   $$R_i(t)=Y_i'(t)+sE(t)+s\int_t^1[E'(r)+sE(r)]\,dr\tag{49}$$
--   are nonnegative, nonincreasing in $t$ and nondecreasing in $i$. Let $H_R=R_m(0)$ and, for $\omega\in[0,H_R]$, $T_i(\omega)=\sup\{t\in[0,1]:R_i(t)>\omega\}$ (with $\sup\varnothing=0$) and $\tau(\omega)=T_0(\omega)$. These endpoints are measurable and satisfy $0\le\tau(\omega)\le T_1(\omega)\le\dots\le T_m(\omega)\le 1$. With
--   $$E_\tau(t)=\frac{e^{-s(t+\tau)}\big(e^{2s\min\{t,\tau\}}-1\big)}{2s},\qquad K_{i,\omega}(t)=\min\{t,T_i(\omega)\}-\min\{t,\tau(\omega)\},\tag{50}$$
--   one has, for $t\in[0,1]$,
--   $$E(t)=\int_0^{H_R}E_{\tau(\omega)}(t)\,d\omega,\qquad K_i(t)=\int_0^{H_R}K_{i,\omega}(t)\,d\omega .$$
--   Moreover $E_\tau'+sE_\tau=r_{0,\tau}$ with $r_{0,\tau}(t)=e^{-s(\tau-t)}\mathbf 1\{t<\tau\}$, and with $r_0=E'+sE$, for $0\le i\le m$ and almost every $t$,
--   $$R_i(t)=\int_0^{H_R}\mathbf 1\{t<T_i(\omega)\}\,d\omega,\qquad r_0(t)=\int_0^{H_R}r_{0,\tau(\omega)}(t)\,d\omega.\tag{51}$$
--   The representation turns the path terms of the proof into nested intervals to which Lemma 4.7 applies.
--
--   Differences from the source:
--   - encoding: objective defined on Q only; R^n with coordinatewise order; C^1 with boundary derivatives the continuous extensions of interior ones → f a total function on EuclideanSpace ℝ (Fin n), hypotheses on the cube only, values off the cube never read; the order written coordinatewise; GeomDRSub.IsDRSubmodular (ContDiffOn ℝ 1 on the cube, fderivWithin the cube); reason: Lean convention; on the cube the within-cube derivative of a C^1 function is the continuous extension of the interior derivative, so the instances are the same
--   - encoding: L includes a dummy coordinate of state 1, label 1, weight q = 1, zero field component → only the original coordinates are represented; the dummy enters as label 1 with q_1 = 1 and its zero terms are dropped; reason: F does not depend on the dummy coordinate (p.10), so every dropped term is zero; same instances
--   - encoding: primes are t-derivatives on [0,1]; almost every t → derivWithin on Set.Icc 0 1; almost everywhere for Lebesgue measure restricted to [0,1]; reason: Lean convention; the paths are C^1 on [0,1]
--   - reading: the endpoints T_i (functions of ω ∈ [0, H_R]) are measurable → the restriction of T_i to [0, H_R] is measurable; reason: the endpoints are defined for levels ω ∈ [0, H_R]
--   - reading: E'_τ + sE_τ = r_{0,τ} → for τ, t ∈ [0,1] with t ≠ τ, derivWithin (E_τ) [0,1] t + sE_τ(t) = r_{0,τ}(t); reason: E_τ has a corner at t = τ (its one-sided derivatives differ by 1 when 0 < τ < 1), so the identity can only hold off t = τ; the page uses it only under integrals
-- source:
--   Aggarwal–Du, 0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular Maximization, arXiv:2610.21072, Lemma 4.8, p.21

import Mathlib
import Definitions.Def_GeomDRSub_IsDRSubmodular
import Definitions.Def_DRSub4633_Ypath
import Definitions.Def_DRSub4633_mLarge
import Definitions.Def_DRSub4633_sPar

namespace DRSub4633

/-- **Lemma 4.8 (Ordered integral representation).** Aggarwal–Du, *0.4633-Approximation for Online and Offline Non-Monotone DR-Submodular
Maximization*, arXiv:2610.21072, Lemma 4.8, p.21: "For `0 ≤ i ≤ m`,
the functions `Rᵢ(t) = Y′ᵢ(t) + sE(t) + s ∫_t^1 [E′(r) + sE(r)] dr` (49) are nonnegative,
nonincreasing in `t`, and nondecreasing in `i`. Let `H_R = R_m(0)` and, for a level `ω ∈ [0, H_R]`,
`Tᵢ(ω) = sup{t ∈ [0, 1] : Rᵢ(t) > ω}` (with `sup ∅ = 0`) and `τ(ω) = T₀(ω)`. These endpoints are
measurable and satisfy `0 ≤ τ(ω) ≤ T₁(ω) ≤ · · · ≤ T_m(ω) ≤ 1`. The corresponding paths are
`E_τ(t) = e^(−s(t+τ))(e^(2s min{t,τ}) − 1)/(2s)`, `K_(i,ω)(t) = min{t, Tᵢ(ω)} − min{t, τ(ω)}`. (50)
Then the paths have the representations `E(t) = ∫_0^(H_R) E_(τ(ω))(t) dω`,
`Kᵢ(t) = ∫_0^(H_R) K_(i,ω)(t) dω`. Moreover `E′_τ + sE_τ = r_(0,τ)`, where
`r_(0,τ)(t) = e^(−s(τ−t)) 1{t < τ}`, and, with `r₀ = E′ + sE`, for `0 ≤ i ≤ m` and almost every `t`,
`Rᵢ(t) = ∫_0^(H_R) 1{t < Tᵢ(ω)} dω`, `r₀(t) = ∫_0^(H_R) r_(0,τ(ω))(t) dω`. (51)"

Standing hypotheses (Sections 3.1 and 4.1, pp.7–10): `f` nonnegative, `C¹` and DR-submodular on
`Q = [0, 1]^n`; `x ∈ Q` is the fixed state.
`Iᵢ = Yᵢ(0)`, `Kᵢ(t) = Yᵢ(t) − Iᵢ − E(t)` (48), `E = Y₀`.

**Formalization Note.** Primes are derivatives within `[0, 1]` (`derivWithin`). The path
statements are for `t ∈ [0, 1]`; "almost every `t`" is for Lebesgue measure on `[0, 1]`.
Measurability of `Tᵢ` is of its restriction to `[0, H_R]`. `E_τ` has a corner at `t = τ` (its one-sided
derivatives differ there when `0 < τ < 1`), so `E′_τ + sE_τ = r_(0,τ)` is stated for `τ, t ∈ [0, 1]`
with `t ≠ τ`. -/
theorem lemma_4_8 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (hf0 : ∀ y ∈ GeomDRSub.cube n, 0 ≤ f y) (hf : GeomDRSub.IsDRSubmodular f)
    (x : EuclideanSpace ℝ (Fin n)) (hx : x ∈ GeomDRSub.cube n) :
    let m : ℕ := mLarge x
    let Y : ℕ → ℝ → ℝ := fun i t => Ypath f x i t
    let E : ℝ → ℝ := Y 0
    let E' : ℝ → ℝ := fun t => derivWithin E (Set.Icc (0 : ℝ) 1) t
    let R : ℕ → ℝ → ℝ := fun i t =>
      derivWithin (Y i) (Set.Icc (0 : ℝ) 1) t + sPar * E t
        + sPar * ∫ r in t..1, (E' r + sPar * E r)
    let HR : ℝ := R m 0
    let T : ℕ → ℝ → ℝ := fun i ω => sSup {t : ℝ | t ∈ Set.Icc (0 : ℝ) 1 ∧ ω < R i t}
    let τ : ℝ → ℝ := T 0
    let Eτ : ℝ → ℝ → ℝ := fun τ' t =>
      Real.exp (-(sPar * (t + τ'))) * (Real.exp (2 * sPar * min t τ') - 1) / (2 * sPar)
    let Kω : ℕ → ℝ → ℝ → ℝ := fun i ω t => min t (T i ω) - min t (τ ω)
    let K : ℕ → ℝ → ℝ := fun i t => Y i t - Y i 0 - E t
    let r0τ : ℝ → ℝ → ℝ := fun τ' t => Real.exp (-(sPar * (τ' - t))) * (if t < τ' then 1 else 0)
    let r0 : ℝ → ℝ := fun t => E' t + sPar * E t
    -- Rᵢ nonnegative, nonincreasing in t, nondecreasing in i
    (∀ i ≤ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ R i t) ∧
    (∀ i ≤ m, AntitoneOn (R i) (Set.Icc (0 : ℝ) 1)) ∧
    (∀ i < m, ∀ t ∈ Set.Icc (0 : ℝ) 1, R i t ≤ R (i + 1) t) ∧
    -- the endpoints are measurable and ordered
    (∀ i ≤ m, Measurable ((Set.Icc (0 : ℝ) HR).domRestrict (T i))) ∧
    (∀ ω ∈ Set.Icc (0 : ℝ) HR, 0 ≤ τ ω ∧ (∀ i < m, T i ω ≤ T (i + 1) ω) ∧ T m ω ≤ 1) ∧
    -- the path representations
    (∀ t ∈ Set.Icc (0 : ℝ) 1, E t = ∫ ω in (0 : ℝ)..HR, Eτ (τ ω) t) ∧
    (∀ i ≤ m, ∀ t ∈ Set.Icc (0 : ℝ) 1, K i t = ∫ ω in (0 : ℝ)..HR, Kω i ω t) ∧
    -- E′_τ + sE_τ = r_(0,τ)
    (∀ τ' ∈ Set.Icc (0 : ℝ) 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, t ≠ τ' →
      derivWithin (Eτ τ') (Set.Icc (0 : ℝ) 1) t + sPar * Eτ τ' t = r0τ τ' t) ∧
    -- (51)
    (∀ i ≤ m, ∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
      R i t = ∫ ω in (0 : ℝ)..HR, (if t < T i ω then (1 : ℝ) else 0)) ∧
    (∀ᵐ t ∂(MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) 1)),
      r0 t = ∫ ω in (0 : ℝ)..HR, r0τ (τ ω) t) := by sorry

end DRSub4633
