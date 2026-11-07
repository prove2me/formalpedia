-- Prove2me | Theorems.Thm_FermiGaussMix_lemma_B_7
-- name    : FermiGaussMix.lemma_B_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:27.88848+00:00
-- url     : https://prove2.me/theorems/2c7a1ab0-9d53-4005-8c43-cfe1a82bd913
-- title:
--   Lemma B.7 — $L_q(M_{S,i}-\mathbf 1)\le\exp\bigl(\eta_q/(1-2d\eta_q/q^2)\bigr)-1$
-- statement:
--   Let $A(u)$ be the interaction-picture operator of a local model with Hermitian sums, $\beta>0$, $T=\beta/2$, $q\ge 1$ and $\eta_q=\int_0^TJ_q(A(u))\,du$. Let $X^S$ solve $\frac{d}{du}X^S=-A^SX^S$, $X^S(0)=\mathbf 1$ on $[0,T]$, for each $S\subseteq[2n]$. If $2d\eta_q/q^2<1$, then for every $S$ and $i\in S$, with $S'=S\setminus\{i\}$ and $M_{S,i}=(X^{S'}(T))^{-1}X^S(T)$,
--   $$
--   L_q(M_{S,i}-\mathbf 1)\le\exp\Bigl(\frac{\eta_q}{1-2d\eta_q/q^2}\Bigr)-1,
--   $$
--   and the same bound holds for $M_{S,i}^\dagger-\mathbf 1$. Both operators are combinations of even monomials supported in $S$. So removing one label changes the evolution by a factor close to the identity in this norm, however large the system.
--
--   Differences from the source:
--   - encoding: X^S(u) = T exp(−∫_0^u A^S(v) dv) → X, X' are any solutions of the ODE in IsPropagator, entrywise derivative on [0, T]; reason: Mathlib has no time-ordered exponential; a solution exists and is unique, so this is the same operator
--   - generalization: the bound (B.92) → also the clauses that M − 1 and M† − 1 lie in the span of even P_R with R ⊆ S; reason: L_q cannot see an odd part; this is (B.13) and the support fact of p. 14
--   - generalization: supports B in balls of radius r0 of a lattice Λ ⊂ Z^D, with at most ν modes per site and each site in at most q_B sets → any finite family of supports B_j ⊆ [2n] with |B_j| ≤ d and each label in at most q_B of them; reason: the lattice enters only through d and q_B; a lattice family is one such family, since a label sits at one site
--   - generalization: K0† = K0 and H a Hamiltonian → only the sums Σ H_{0,j} and Σ V_j are assumed Hermitian, not the local terms; reason: the Hermitian local terms of the page are a special case
--   - generalization: additive constants omitted from H, so X^∅ = 1 (B.81) → V_j may contain a scalar term (R = ∅ is even); reason: the page's case is scalar-free; a scalar does not change ρ_β or any coefficient with R ≠ ∅
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, Lemma B.7, p. 21

import Mathlib
import Definitions.Def_FermiGaussMix_IsLocalModel
import Definitions.Def_FermiGaussMix_IsPropagator

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Lemma B.7, p.21** (Han, Zhao, Liu, arXiv:2609.35159v1). Let `T = β/2`, `A = A(u)` the interaction-picture
operator of a local model, `q ≥ 1` and `η_q = ∫_0^T J_q(A(u)) du`. If `2 d η_q / q² < 1`, then for every `S ⊆ [N]` and
`i ∈ S`, with `S' = S \ {i}` and `M_{S,i} = (X^{S'})^{-1} X^S`,
`L_q(M_{S,i} - 1) ≤ exp(η_q / (1 - 2dη_q/q²)) - 1`, and the same bound holds for `M_{S,i}† - 1`.

**Formalization Note** `X^S` and `X^{S'}` are arbitrary solutions of their equations (B.80); a solution exists and is
unique. A solution of a linear equation is invertible, so the matrix inverse is not a junk value. `J_q(A(u))` is continuous
in `u`, so the integral is not a junk value either. `L_q` cannot see an odd part, so the conclusion also states that
`M_{S,i} - 1` and its adjoint lie in the span of the even `P_R` with `R ⊆ S` (the expansion (B.13) and the support fact of
p.14). -/
theorem lemma_B_7 {n m d qB : ℕ} {g β q : ℝ} {B : Fin m → Finset (Fin (2 * n))} {H0 V : Fin m → Op n}
    (hm : IsLocalModel d qB g B H0 V)
    (hH0 : (∑ j, H0 j)ᴴ = ∑ j, H0 j) (hV : (∑ j, V j)ᴴ = ∑ j, V j)
    (hβ : 0 < β) (hq : 1 ≤ q)
    (hη : 2 * (d : ℝ) * etaQ q (β / 2) (interaction (∑ j, H0 j) (∑ j, V j)) / q ^ 2 < 1)
    (S : Finset (Fin (2 * n))) (i : Fin (2 * n)) (hi : i ∈ S) (X X' : ℝ → Op n)
    (hX : IsPropagator (β / 2) (fun u => restrict S (interaction (∑ j, H0 j) (∑ j, V j) u)) X)
    (hX' : IsPropagator (β / 2)
      (fun u => restrict (S.erase i) (interaction (∑ j, H0 j) (∑ j, V j) u)) X') :
    (X' (β / 2))⁻¹ * X (β / 2) - 1 ∈ evenSpan S ∧
    ((X' (β / 2))⁻¹ * X (β / 2))ᴴ - 1 ∈ evenSpan S ∧
    Lq q ((X' (β / 2))⁻¹ * X (β / 2) - 1) ≤
      Real.exp (etaQ q (β / 2) (interaction (∑ j, H0 j) (∑ j, V j)) /
        (1 - 2 * (d : ℝ) * etaQ q (β / 2) (interaction (∑ j, H0 j) (∑ j, V j)) / q ^ 2)) - 1 ∧
    Lq q (((X' (β / 2))⁻¹ * X (β / 2))ᴴ - 1) ≤
      Real.exp (etaQ q (β / 2) (interaction (∑ j, H0 j) (∑ j, V j)) /
        (1 - 2 * (d : ℝ) * etaQ q (β / 2) (interaction (∑ j, H0 j) (∑ j, V j)) / q ^ 2)) - 1 := by sorry

end FermiGaussMix
