-- Prove2me | Theorems.Thm_FermiGaussMix_eq_A_9_A_10
-- name    : FermiGaussMix.eq_A_9_A_10
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T20:59:34.878302+00:00
-- url     : https://prove2.me/theorems/73dadc9c-9626-4c49-a307-ab698d0bc0b0
-- title:
--   Eqs. (A.9)–(A.10) — row and column sums of $K_0$, and $\max_a\sum_{R\ni a}|v_R|\le C_Vg$
-- statement:
--   Let $H_0=\sum_jH_{0,j}$ and $V=\sum_jV_j$ come from a local model with constants $d,q_B,g$, with $H_0$ Hermitian. The matrix $K_0$ read off from the coefficients of $H_0$ satisfies $K_0^{T}=-K_0$, $K_0^\dagger=K_0$ and $H_0=\frac14\gamma^TK_0\gamma$, and
--   $$
--   \max\{\|K_0\|_{1\to1},\|K_0\|_{\infty\to\infty}\}\le 2q_B(d-1)=C_H .
--   $$
--   Writing $V=\sum_Rv_RP_R$,
--   $$
--   \max_a\sum_{R\ni a}|v_R|\le q_B2^dg=C_Vg .
--   $$
--   These constants control how a Majorana operator spreads under the quadratic evolution and how much interaction weight passes through one label.
--
--   **Formalization Note** The two induced norms are written as maximal column and row sums.
--
--   Differences from the source:
--   - generalization: supports B in balls of radius r0 of a lattice Λ ⊂ Z^D, with at most ν modes per site and each site in at most q_B sets → any finite family of supports B_j ⊆ [2n] with |B_j| ≤ d and each label in at most q_B of them; reason: the lattice enters only through d and q_B; a lattice family is one such family, since a label sits at one site
--   - generalization: K0† = K0 and H a Hamiltonian → only the sum Σ H_{0,j} is assumed Hermitian, not the local terms, and no Hermiticity of V is assumed; reason: the Hermitian local terms of the page are a special case, and (A.10) does not use Hermiticity of V
--   - encoding: K0 given with H0 = (1/4) γ^T K0 γ (A.4) → K0 defined from the coefficients of H0 by the identity of p. 9, with the clauses K0ᵀ = −K0, K0ᴴ = K0 and H0 = (1/4) γ^T K0 γ as conclusions; reason: an antisymmetric K0 is determined by H0
--   - encoding: C_H = 2q_B(d − 1) → d − 1 is natural-number subtraction, so C_H = 0 at d = 0; reason: the same for d ≥ 1; at d = 0 every support is empty and the printed value would be negative
--   - generalization: additive constants omitted from H → V_j may contain a scalar term (R = ∅ is even); reason: the page's case is scalar-free; the sums in (A.10) run over R ∋ a, so a scalar term does not enter them
--   - encoding: Majorana operators γ_a satisfying (A.1) → the published Jordan–Wigner operators FermiCap.Gaussian.majorana, labels Fin (2 * n), 0-based; reason: any family with (A.1) on a 2^n-dimensional space is unitarily equivalent to this one, and all objects here are unitarily covariant
-- source:
--   Han, Zhao, Liu, Weakly interacting fermionic Gibbs states are Gaussian mixtures and classically simulable, arXiv:2609.35159v1, eqs. (A.9)–(A.10), pp. 9–10

import Mathlib
import Definitions.Def_FermiGaussMix_coeff
import Definitions.Def_FermiGaussMix_IsLocalModel

open scoped BigOperators Matrix.Norms.L2Operator
open Matrix FermiCap.Gaussian

namespace FermiGaussMix

/-- **Eqs. (A.9)–(A.10), pp.9–10** (Han, Zhao, Liu, arXiv:2609.35159v1). For a local model with `H₀ = Σ_j H_{0,j}`
Hermitian and `V = Σ_j V_j`, the matrix `K₀` of (A.4) is antisymmetric and Hermitian with `H₀ = ¼ γᵀK₀γ`, its row and
column sums are at most `C_H = 2q_B(d-1)`, and `max_a Σ_{R∋a} |v_R| ≤ C_V g` with `C_V = q_B 2^d`.

**Formalization Note** `‖K₀‖_{∞→∞}` is the maximal row sum and `‖K₀‖_{1→1}` the maximal column sum. `K₀` is read off
from `H₀` through the coefficient identity of p.9 (`K0`), and the first clauses state that it is the paper's matrix. -/
theorem eq_A_9_A_10 {n m d qB : ℕ} {g : ℝ} {B : Fin m → Finset (Fin (2 * n))} {H0 V : Fin m → Op n}
    (hm : IsLocalModel d qB g B H0 V) (hH0 : (∑ j, H0 j)ᴴ = ∑ j, H0 j) :
    (K0 (∑ j, H0 j))ᵀ = -K0 (∑ j, H0 j) ∧
    (K0 (∑ j, H0 j))ᴴ = K0 (∑ j, H0 j) ∧
    ∑ j, H0 j = (4 : ℂ)⁻¹ • ∑ a, ∑ b, K0 (∑ j, H0 j) a b • (majorana n a * majorana n b) ∧
    (∀ a, ∑ b, ‖K0 (∑ j, H0 j) a b‖ ≤ CH qB d) ∧
    (∀ b, ∑ a, ‖K0 (∑ j, H0 j) a b‖ ≤ CH qB d) ∧
    (∀ a, ∑ R ∈ (evenSets n).filter (fun R => a ∈ R), ‖coeff (∑ j, V j) R‖ ≤ CV qB d * g) := by sorry

end FermiGaussMix
