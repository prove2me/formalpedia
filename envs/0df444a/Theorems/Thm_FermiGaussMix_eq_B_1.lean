-- Prove2me | Theorems.Thm_FermiGaussMix_eq_B_1
-- name    : FermiGaussMix.eq_B_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:09.759913+00:00
-- url     : https://prove2.me/theorems/0e5fbeb2-f23c-4ef7-97f3-a38a3f3bb6d8
-- title:
--   Eqs. (B.1), (B.65) — $e^{-\beta H}=GXX^\dagger G$, $G$ is Gaussian, and $X'=-AX$
-- statement:
--   Let $H_0$ be Hermitian and quadratic, $V$ Hermitian and even, $H=H_0+V$, $\beta>0$, $T=\beta/2$. With $G=e^{-TH_0}$ and $X=e^{TH_0}e^{-TH}$,
--   $$
--   e^{-\beta H}=GXX^\dagger G .
--   $$
--   The operator $G$ is an invertible positive Gaussian operator. The family $X(u)=e^{uH_0}e^{-uH}$ solves
--   $$
--   \frac{d}{du}X(u)=-A(u)X(u),\qquad X(0)=\mathbf 1,\qquad A(u)=e^{uH_0}Ve^{-uH_0},
--   $$
--   on $[0,T]$, and $A(u)$ is its own part supported in $[2n]$, which gives $X^{[N]}=X$. This factorization reduces the theorem to the positive middle operator $XX^\dagger$.
--
--   Differences from the source:
--   - generalization: H0, V of the local model (A.4)–(A.6) → any Hermitian quadratic H0 and any Hermitian even V, with no locality; reason: a local model is a special case
--   - generalization: (B.1), (B.65), and the phrase "since G is Gaussian" → also the clauses that G is PosDef and IsNonnegGaussian, and that restricting A(u) to S = [N] gives A(u); reason: the proof of Theorem A.1 uses them; p. 11 asserts the first and (B.81) the second
--   - encoding: X^S(u) = T exp(−∫_0^u A^S(v) dv) → X, X' are any solutions of the ODE in IsPropagator, entrywise derivative on [0, T]; reason: Mathlib has no time-ordered exponential; a solution exists and is unique, so this is the same operator
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, eq. (B.1), p. 11, and eq. (B.65), p. 18

import Mathlib
import Definitions.Def_FermiGaussMix_gibbs
import Definitions.Def_FermiGaussMix_IsPropagator

open scoped BigOperators ComplexOrder
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Eqs. (B.1), p.11, and (B.65), p.18** (Han, Zhao, Liu, arXiv:2609.35159v1). With `T = β/2` and `H = H₀ + V`:
`e^{-βH} = G X X† G`, where `G = e^{-T H₀}` and `X = e^{T H₀} e^{-T H}`. Moreover `G` is an invertible positive
Gaussian operator ("since `G` is Gaussian", p.11); `X(u)` solves `X' = -A X`, `X(0) = 1` on `[0, T]`; and `A^{[N]} = A`,
so that `X^{[N]} = X` (B.81).

**Formalization Note** No locality is needed: `H₀` is any Hermitian quadratic operator and `V` any Hermitian even
operator. -/
theorem eq_B_1 {n : ℕ} {β : ℝ} {H0 V : Op n} (hβ : 0 < β)
    (hH0 : H0ᴴ = H0) (hquad : H0 ∈ quadraticSpan (Finset.univ : Finset (Fin (2 * n))))
    (hV : Vᴴ = V) (heven : IsEvenOp V) :
    NormedSpace.exp ((-β : ℂ) • (H0 + V)) =
      gOp (β / 2) H0 * (xOp (β / 2) H0 V * (xOp (β / 2) H0 V)ᴴ) * gOp (β / 2) H0 ∧
    (gOp (β / 2) H0).PosDef ∧
    IsNonnegGaussian (gOp (β / 2) H0) ∧
    IsPropagator (β / 2) (interaction H0 V) (fun u => xOp u H0 V) ∧
    (∀ u : ℝ, restrict Finset.univ (interaction H0 V u) = interaction H0 V u) := by sorry

end FermiGaussMix
