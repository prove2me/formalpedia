-- Prove2me | Theorems.Thm_FermiGaussMix_lemma_B_2
-- name    : FermiGaussMix.lemma_B_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:01:14.132304+00:00
-- url     : https://prove2.me/theorems/da2d0824-f715-439e-916a-e1ebaf761191
-- title:
--   Lemma B.2 — for $g\le g_{\mathrm{mix}}$, $L_2(M_{S,i}-\mathbf 1)\le 1/12$ and likewise for the adjoint
-- statement:
--   In the setting of Lemma B.7, if $g\le g_{\mathrm{mix}}$, then for every $S\subseteq[2n]$ and $i\in S$,
--   $$
--   M_{S,i}-\mathbf 1=\sum_Rm_RP_R,\qquad M_{S,i}^\dagger-\mathbf 1=\sum_R\tilde m_RP_R,
--   $$
--   over even $R\subseteq S$, with
--   $$
--   \sum_R|m_R|2^{|R|}\le\frac1{12},\qquad\sum_R|\tilde m_R|2^{|R|}\le\frac1{12}.
--   $$
--   The constant is independent of $S$, $i$ and the system size. It is what keeps the operators in the convex decomposition nonnegative.
--
--   Differences from the source:
--   - generalization: there is a constant r ≤ 1/12, independent of S, i and the system size → the bounds with r = 1/12; reason: this is the value of (B.113) and implies the existential, uniformly by quantifier order
--   - generalization: g ≤ g_mix = η_mix/(2^d C_V I_β), η_mix = min{1/d, (1/2) log(13/12)} → BelowThreshold: d·η ≤ 1 and η ≤ (1/2) log(13/12) with η = 2^d C_V I_β g; reason: identical for d, q_B ≥ 1 and β > 0; for d = 0 or q_B = 0 the printed quotient is undefined and the product form reads 1/0 as +∞
--   - encoding: X^S(u) = T exp(−∫_0^u A^S(v) dv) → X, X' are any solutions of the ODE in IsPropagator, entrywise derivative on [0, T]; reason: Mathlib has no time-ordered exponential; a solution exists and is unique, so this is the same operator
--   - generalization: supports B in balls of radius r0 of a lattice Λ ⊂ Z^D, with at most ν modes per site and each site in at most q_B sets → any finite family of supports B_j ⊆ [2n] with |B_j| ≤ d and each label in at most q_B of them; reason: the lattice enters only through d and q_B; a lattice family is one such family, since a label sits at one site
--   - generalization: K0† = K0 and H a Hamiltonian → only the sums Σ H_{0,j} and Σ V_j are assumed Hermitian, not the local terms; reason: the Hermitian local terms of the page are a special case
--   - generalization: additive constants omitted from H, so X^∅ = 1 (B.81) → V_j may contain a scalar term (R = ∅ is even); reason: the page's case is scalar-free; a scalar does not change ρ_β or any coefficient with R ≠ ∅
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, Lemma B.2, p. 13, with the value of r from eq. (B.113), p. 23

import Mathlib
import Definitions.Def_FermiGaussMix_IsLocalModel
import Definitions.Def_FermiGaussMix_IsPropagator

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Lemma B.2, p.13** (Han, Zhao, Liu, arXiv:2609.35159v1). If `g ≤ g_mix`, then for every `S ⊆ [N]` and `i ∈ S`,
`M_{S,i} - 1 = Σ_R m_R P_R` and `M_{S,i}† - 1 = Σ_R m̃_R P_R` with `Σ_R |m_R| 2^{|R|} ≤ r`, `Σ_R |m̃_R| 2^{|R|} ≤ r`.

**Formalization Note** The page says "there is a constant `r ≤ 1/12`, independent of `S`, `i`, and the system size". The
statement takes the page's value `r = 1/12` from (B.113), which is uniform by quantifier order and implies the existential.
The expansion (B.13) is the span clause; its coefficients are `coeff` by Eq. (A.8). -/
theorem lemma_B_2 {n m d qB : ℕ} {g β : ℝ} {B : Fin m → Finset (Fin (2 * n))} {H0 V : Fin m → Op n}
    (hm : IsLocalModel d qB g B H0 V)
    (hH0 : (∑ j, H0 j)ᴴ = ∑ j, H0 j) (hV : (∑ j, V j)ᴴ = ∑ j, V j)
    (hβ : 0 < β) (hg : BelowThreshold d qB β g)
    (S : Finset (Fin (2 * n))) (i : Fin (2 * n)) (hi : i ∈ S) (X X' : ℝ → Op n)
    (hX : IsPropagator (β / 2) (fun u => restrict S (interaction (∑ j, H0 j) (∑ j, V j) u)) X)
    (hX' : IsPropagator (β / 2)
      (fun u => restrict (S.erase i) (interaction (∑ j, H0 j) (∑ j, V j) u)) X') :
    (X' (β / 2))⁻¹ * X (β / 2) - 1 ∈ evenSpan S ∧
    ((X' (β / 2))⁻¹ * X (β / 2))ᴴ - 1 ∈ evenSpan S ∧
    Lq 2 ((X' (β / 2))⁻¹ * X (β / 2) - 1) ≤ 1 / 12 ∧
    Lq 2 (((X' (β / 2))⁻¹ * X (β / 2))ᴴ - 1) ≤ 1 / 12 := by sorry

end FermiGaussMix
