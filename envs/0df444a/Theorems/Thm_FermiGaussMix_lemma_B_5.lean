-- Prove2me | Theorems.Thm_FermiGaussMix_lemma_B_5
-- name    : FermiGaussMix.lemma_B_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T21:00:56.623639+00:00
-- url     : https://prove2.me/theorems/037b76dd-3782-440f-911a-a8514f3d4576
-- title:
--   Lemma B.5 — $J_q(A(u))\le q^dC_Vg\,e^{dC_Hu}$
-- statement:
--   Let $H_0=\sum_jH_{0,j}$ and $V=\sum_jV_j$ come from a local model, with both sums Hermitian, and let $A(u)=e^{uH_0}Ve^{-uH_0}$. For every $q\ge 1$ and $u\ge 0$,
--   $$
--   J_q(A(u))\le q^dC_Vg\,e^{dC_Hu}.
--   $$
--   In addition $A(u)$ is even, and every Majorana monomial in it has degree at most $d$. The bound does not depend on the system size, although the quadratic conjugation spreads a local monomial over the whole system.
--
--   Differences from the source:
--   - generalization: 0 ≤ u ≤ T → every u ≥ 0; reason: the printed range is contained in it, and T does not occur in the bound
--   - generalization: the bound (B.71) → also the clauses that A(u) is even and has degree at most d; reason: J_q cannot see them and later lemmas use them; p. 21 states "the quadratic evolution preserves Majorana degree"
--   - generalization: supports B in balls of radius r0 of a lattice Λ ⊂ Z^D, with at most ν modes per site and each site in at most q_B sets → any finite family of supports B_j ⊆ [2n] with |B_j| ≤ d and each label in at most q_B of them; reason: the lattice enters only through d and q_B; a lattice family is one such family, since a label sits at one site
--   - generalization: K0† = K0 and H a Hamiltonian → only the sums Σ H_{0,j} and Σ V_j are assumed Hermitian, not the local terms; reason: the Hermitian local terms of the page are a special case
--   - generalization: additive constants omitted from H, so X^∅ = 1 (B.81) → V_j may contain a scalar term (R = ∅ is even); reason: the page's case is scalar-free; a scalar does not change ρ_β or any coefficient with R ≠ ∅
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, Lemma B.5, p. 19

import Mathlib
import Definitions.Def_FermiGaussMix_IsLocalModel
import Definitions.Def_FermiGaussMix_IsPropagator

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Lemma B.5, p.19** (Han, Zhao, Liu, arXiv:2609.35159v1). For every `q ≥ 1` and `u ≥ 0`,
`J_q(A(u)) ≤ q^d C_V g e^{d C_H u}`, where `A(u) = e^{u H₀} V e^{-u H₀}`.

**Formalization Note** The page has `0 ≤ u ≤ T`, and the proof does not use `u ≤ T`. Two clauses are added because the
later lemmas use them and `Jq` cannot see them: `A(u)` is even, and its monomials have degree at most `d` ("the quadratic
evolution preserves Majorana degree", p.21). -/
theorem lemma_B_5 {n m d qB : ℕ} {g : ℝ} {B : Fin m → Finset (Fin (2 * n))} {H0 V : Fin m → Op n}
    (hm : IsLocalModel d qB g B H0 V)
    (hH0 : (∑ j, H0 j)ᴴ = ∑ j, H0 j) (hV : (∑ j, V j)ᴴ = ∑ j, V j)
    {q u : ℝ} (hq : 1 ≤ q) (hu : 0 ≤ u) :
    IsEvenOp (interaction (∑ j, H0 j) (∑ j, V j) u) ∧
    HasDegreeLE d (interaction (∑ j, H0 j) (∑ j, V j) u) ∧
    Jq q (interaction (∑ j, H0 j) (∑ j, V j) u) ≤
      q ^ d * CV qB d * g * Real.exp ((d : ℝ) * CH qB d * u) := by sorry

end FermiGaussMix
