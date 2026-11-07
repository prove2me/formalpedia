-- Prove2me | Theorems.Thm_BeyondDS_section_8_4
-- name    : BeyondDS.section_8_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T16:14:19.434467+00:00
-- url     : https://prove2.me/theorems/046f30f3-dddb-4dba-bc08-8a326534e2ac
-- title:
--   §8.4, (28)–(32) — failure probability, $\mathbb E[N]$, $\mathbb E[M]$ and $\mathbb E[T]$ of the compiler
-- statement:
--   For the compiler with $\lambda\ge1024\log(n+1)$, a perfectly correct scheme, any adversary, and an election law at statistical distance at most $\zeta$ from uniform with $q=1/2+\zeta+6\delta<1$, let $Q=6J+4$, $\epsilon=\Pr[\mathrm{Forge}]$ in this execution, and $\beta=Q\delta+\epsilon$. Then
--
--   $$\Pr[\text{relevant failure}]\le\beta,\qquad \mathbb E[N]\le1+\frac1{1-q}+J\beta,\qquad \Pr[\text{broadcast failure}]\le q^J+\beta,$$
--
--   $M\le D=(6J+4)(6nH+n^2)$ on every history, and
--
--   $$\mathbb E[M]\le c_A(6\mathbb E[N]+4)+c_T+D\beta,\qquad \mathbb E[T]\le7(6\mathbb E[N]+4)+9+7Q\beta,\qquad T\le7Q .$$
--
--   These are the estimates from which Theorem 8 follows by choosing $J=\lceil c\lambda\rceil$.
--
--   **Formalization Note** All bounds are in $[0,\infty]$, unconditional, for every adversary; $c_A,c_T$ are the values of (27).
--
--   Differences from the source:
--
--   - encoding: ϵ, "the aggregate signature-forgery probability for the capped execution" → the probability of the forgery event in this execution; reason: same quantity
--   - reading: "relevant statistical or authentication failure" → a forgery, a statistical delivery failure or epoch failure of a call up to g, or a first-epoch failure of the call after g; reason: the list of p.32
--   - reading: cA, cT in (31) → the right-hand sides of (27), and n(n − 1), 2n(n − 1) in the dense case; reason: Lemma 8.1 supplies them
--   - encoding: signatures → a perfectly correct scheme; reason: the standing assumption of the paper's model (decision 7)
-- source:
--   Rambaud, Beyond Dolev–Strong, STOC 2027 submission (manuscript sha256 c84cf9c9…), §8.4, pp.32–33 (PDF pp.33–34), eqs. (28)–(32)

import Mathlib
import Definitions.Def_BeyondDS_DeliveryFail

set_option autoImplicit false

open QAlgorithms.Complexity
open scoped ENNReal
open Polynomial

namespace BeyondDS

/-- The failure and cost accounting of Rambaud, *Beyond Dolev–Strong*, STOC 2027 submission (manuscript sha256 c84cf9c9…), §8.4, pp.32–33 (PDF 33–34), eqs. (28)–(32): there are at most `Q = 6J + 4` scheduled calls, and `N` counts main iterations begun before `g`, capped at `J`. For an oracle at statistical distance at most `ζ` from the prescribed conditional uniform distribution, with `β = Qδ + ϵ` and
`q = 1/2 + ζ + 6δ < 1`, the probability of any relevant statistical or authentication failure is at most `β`; `E[N] ≤ 1 + 1/(1 − q) + Jβ` and `Pr[broadcast failure] ≤ q^J + β`; with `D = (6J + 4)(6nH + n²)`, `H = min{K, n}`, which bounds all honest-sent messages on every history, `E[M] ≤ cA(6E[N] + 4) + cT + Dβ`; and
`E[T] ≤ 7(6E[N] + 4) + 9 + 7Qβ`, `T ≤ 7Q`.

**Formalization Note.** `ϵ` is `prob D Forge`, one number of this execution. `cA`, `cT` are the right sides of (27) (Lemma 8.1), in the dense case `n(n − 1)` and `2n(n − 1)`, and `δ = 0` in the dense case. All bounds are in `[0, ∞]`, unconditional, for every adversary. -/
theorem section_8_4 (J : Params → ℕ) (S : Sig) (hS : S.Correct) (P : Params) (x : Bool) (ζ : ℝ)
    (E : List (Event P.n CMsg CSt) → PMF (Fin P.n)) (hE : ElectNear P ζ E) (A : Adversary P.n CMsg CSt)
    (hlam : 1024 * Real.log ((P.n : ℝ) + 1) ≤ P.lam) (hq : qVal P ζ < 1) :
    let D := exec (compiler J) S P x E A
    let Q : ℕ := 6 * J P + 4
    let β : ENNReal := ENNReal.ofReal ((Q : ℝ) * bigDelta P) + prob D {ω | Forge ω}
    let EN : ENNReal := expect D (itersBegun (J P))
    prob D {ω | RelevantFailure P (J P) ω} ≤ β ∧
    EN ≤ ENNReal.ofReal (1 + 1 / (1 - qVal P ζ)) + (J P : ENNReal) * β ∧
    prob D {ω | Fail P x ω} ≤ ENNReal.ofReal (qVal P ζ ^ J P) + β ∧
    (∀ ω ∈ D.support, msgCount ω ≤ bigD P (J P)) ∧
    expect D msgCount ≤
      ENNReal.ofReal (cA P) * (6 * EN + 4) + ENNReal.ofReal (cT P) + (bigD P (J P) : ENNReal) * β ∧
    expect D (roundsUsed (compiler J) P) ≤ 7 * (6 * EN + 4) + 9 + 7 * (Q : ENNReal) * β ∧
    (∀ ω ∈ D.support, roundsUsed (compiler J) P ω ≤ 7 * Q) := by sorry

end BeyondDS
