-- Prove2me | Theorems.Thm_BeyondDS_theorem_8
-- name    : BeyondDS.theorem_8
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:15:00.739198+00:00
-- url     : https://prove2.me/theorems/ffc7088a-56bf-4691-a7b1-87333633916e
-- title:
--   Theorem 8 — adaptive Byzantine broadcast with $O(a+Jn^2\epsilon)$ messages and $O(1+J\epsilon)$ rounds
-- statement:
--   For every $q_0<1$ there is $c_0>0$ such that for every $c\ge c_0$, with $J=\lceil c\lambda\rceil$, there are constants $c',C_1,C_2>0$ with the following. For every perfectly correct scheme, every $n=2t+1$ with $\lambda\ge1024\log(n+1)$, every input bit, every election law at distance at most $\zeta$ from uniform with $q\le q_0$, and every adversary, writing $a=n\min\{n,\sqrt{n\lambda}\}$ and $\epsilon=\Pr[\mathrm{Forge}]$:
--
--   $$\Pr[\text{broadcast failure}]\le e^{-c'\lambda}+\epsilon,\qquad \mathbb E[M]\le C_1(a+Jn^2\epsilon),\qquad \mathbb E[T]\le C_2(1+J\epsilon),$$
--
--   and $T\le7(6J+4)$ on every history. Moreover, if $t_\kappa+\lambda_\kappa$ is polynomially bounded in $\kappa$ and the forgery probability is negligible, then $\mathbb E[M]\le C_1a_\kappa+\nu(\kappa)$ and $\mathbb E[T]\le C_2+\nu(\kappa)$ for a negligible $\nu$.
--
--   "No setup implementing the election oracle from public-key registration alone is asserted."
--
--   **Formalization Note** "Bounded away from one" is the bound $q\le q_0$; since $\delta\ge0$ it makes $\zeta\le q_0-1/2$ a constant below $1/2$. The negligible clause takes the forgery bound as a hypothesis; §4.2's authentication bound discharges it.
--
--   Differences from the source:
--
--   - reading: "choose λ … large enough that q in (28) is bounded away from one", "ζ bounded by a constant strictly below 1/2" → ∀ q₀ < 1, constants depending on q₀, for all instances with q ≤ q₀; reason: "bounded away from one" is a uniform bound below 1, and q ≤ q₀ gives ζ ≤ q₀ − 1/2 < 1/2
--   - encoding: exp(−Ω(λ)), O(·) and "a sufficiently large constant c" → ∃ c₀, ∀ c ≥ c₀, ∃ constants c′, C₁, C₂ > 0; reason: the meaning of the notation
--   - generalization: the theorem's bounds → the same bounds and also T ≤ 7(6J + 4) on every history; reason: the proof states "the public cap supplies an O(J) bound on every history", and dropping the conjunct gives the theorem
--   - encoding: signatures → a perfectly correct scheme; reason: the standing assumption of the paper's model (decision 7)
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), Theorem 8, p.33 (PDF p.34), eq. (33)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail
import Definitions.Def_BeyondDS_EUFCMA

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- Theorem 8 (Adaptive Byzantine broadcast), Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), p.33 (PDF 34), eq. (33): for `n = 2t + 1`, `λ ≥ 1024 log(n + 1)` large enough that `q` of (28) is bounded away from one, and `J = ⌈cλ⌉` for a sufficiently large constant `c`, the compiler, adaptive dissemination and terminal procedure solve Byzantine broadcast with error `exp(−Ω(λ)) + ϵ`. Writing `a = n min{n, √(nλ)}`, the expected number of honest-sent messages is
`O(a + Jn²ϵ)`, and the expected time until all honest sending stops is `O(1 + Jϵ)` rounds. If `n` and `λ` are polynomially bounded in the signature security parameter and `ϵ` is negligible in that parameter, these bounds are expected `O(a)` messages and `O(1)` rounds, up to negligible additive terms. "No setup implementing the election oracle from public-key registration alone is asserted."

**Formalization Note.** "Bounded away from one": for each `q₀ < 1` the constants depend only on `q₀`, for all `P` and `ζ` with `q ≤ q₀`; since `δ ≥ 0`, this makes `ζ ≤ q₀ − 1/2` a constant below `1/2`. The clause `T ≤ 7Q = O(J)` is "the public cap supplies an O(J) bound on every history" from the proof. The negligible clause takes `ϵ` as a hypothesis, unlike the goal Theorem 1; Section 4.2's authentication bound is what discharges it. -/
theorem theorem_8 :
    ∀ q₀ : ℝ, q₀ < 1 → ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ c : ℝ, c₀ ≤ c →
      ∃ c' C₁ C₂ : ℝ, 0 < c' ∧ 0 < C₁ ∧ 0 < C₂ ∧
        (∀ (S : Sig) (P : Params) (x : Bool) (ζ : ℝ) (E : List (Event P.n CMsg CSt) → PMF (Fin P.n))
          (A : Adversary P.n CMsg CSt),
          S.Correct → ElectNear P ζ E → 1024 * Real.log ((P.n : ℝ) + 1) ≤ P.lam → qVal P ζ ≤ q₀ →
          let J : Params → ℕ := fun P' => ⌈c * P'.lam⌉₊
          let D := exec (compiler J) S P x E A
          let ε := prob D {ω | Forge ω}
          prob D {ω | Fail P x ω} ≤ ENNReal.ofReal (Real.exp (-(c' * P.lam))) + ε ∧
          expect D msgCount ≤ ENNReal.ofReal C₁ *
            (ENNReal.ofReal (P.n * min (P.n : ℝ) (Real.sqrt ((P.n : ℝ) * P.lam))) +
              ((J P * P.n ^ 2 : ℕ) : ENNReal) * ε) ∧
          expect D (roundsUsed (compiler J) P) ≤ ENNReal.ofReal C₂ * (1 + (J P : ENNReal) * ε) ∧
          (∀ ω ∈ D.support, roundsUsed (compiler J) P ω ≤ 7 * (6 * J P + 4))) ∧
        (∀ (Sg : ℕ → Sig) (Pf : ℕ → Params) (X : ℕ → Bool) (ζ : ℕ → ℝ)
          (E : (κ : ℕ) → List (Event (Pf κ).n CMsg CSt) → PMF (Fin (Pf κ).n))
          (A : (κ : ℕ) → Adversary (Pf κ).n CMsg CSt) (p : ℕ[X]) (ν₀ : ℕ → ℝ),
          (∀ κ, (Sg κ).Correct) → (∀ κ, ElectNear (Pf κ) (ζ κ) (E κ)) →
          (∀ κ, 1024 * Real.log (((Pf κ).n : ℝ) + 1) ≤ (Pf κ).lam) → (∀ κ, qVal (Pf κ) (ζ κ) ≤ q₀) →
          (∀ κ, (Pf κ).t + (Pf κ).lam ≤ p.eval κ) → Negligible ν₀ →
          let J : Params → ℕ := fun P' => ⌈c * P'.lam⌉₊
          (∀ κ, prob (exec (compiler J) (Sg κ) (Pf κ) (X κ) (E κ) (A κ)) {ω | Forge ω} ≤ ENNReal.ofReal (ν₀ κ)) →
          ∃ ν, Negligible ν ∧ ∀ κ,
            expect (exec (compiler J) (Sg κ) (Pf κ) (X κ) (E κ) (A κ)) msgCount ≤
              ENNReal.ofReal (C₁ * ((Pf κ).n * min ((Pf κ).n : ℝ) (Real.sqrt (((Pf κ).n : ℝ) * (Pf κ).lam))) + ν κ) ∧
            expect (exec (compiler J) (Sg κ) (Pf κ) (X κ) (E κ) (A κ)) (roundsUsed (compiler J) (Pf κ)) ≤
              ENNReal.ofReal (C₂ + ν κ)) := by sorry

end BeyondDS
