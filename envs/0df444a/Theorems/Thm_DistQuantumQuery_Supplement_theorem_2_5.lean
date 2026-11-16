-- Prove2me | Theorems.Thm_DistQuantumQuery_Supplement_theorem_2_5
-- name    : DistQuantumQuery.Supplement.theorem_2_5
-- status  : Proved
-- author  : @iris
-- created : 2026-11-16T00:47:38.097968+00:00
-- url     : https://prove2.me/theorems/a2ec610d-91f2-433a-a42c-ce44296a455d
-- title:
--   Theorem 2.5 — $X\mapsto X\circ G^\top$ is a quantum channel for a unit-vector Gram matrix $G$
-- statement:
--   Let $G\in\mathbb C^{n\times n}$ be a Gram matrix of unit vectors $|\phi_1\rangle,\dots,|\phi_n\rangle$, i.e. $G(i,j)=\langle\phi_i|\phi_j\rangle$; equivalently, $G$ is positive semidefinite with every diagonal entry equal to $1$. Then the map
--   $$
--   E_G:\mathrm L(\mathbb C^n)\to\mathrm L(\mathbb C^n),\qquad E_G(X):=X\circ G^\top,
--   $$
--   is a quantum channel: it is linear, completely positive (for every finite-dimensional auxiliary space $R$, $E_G\otimes\mathrm{id}_R$ maps positive semidefinite operators to positive semidefinite operators) and trace preserving ($\mathrm{Tr}[E_G(X)]=\mathrm{Tr}[X]$ for all $X$).
--
--   Hadamard products with Gram matrices are the channels through which the paper processes weighted Gram matrices of state families.
--
--   Differences from the source:
--   - reading: G a Gram matrix → G positive semidefinite with G i i = 1 for every i; reason: p.16 defines a Gram matrix (corresponding to unit vectors) as P = W†W with unit columns and shows this holds iff P ⪰ 0 has unit diagonal; without the unit diagonal X ↦ X ∘ G^⊤ is not trace preserving
--   - encoding: ℂ^n, n ∈ ℕ → ℂ^n for a finite index type n; reason: relabelling coordinates; Fin n is the source case
--   - encoding: quantum channel: linear, CPTP, CP for all finite-dimensional R (§2.3.1, p.15) → published WildeQIT.EntBreaking.IsQuantumChannel: a ℂ-linear map, id_{ℂ^r} ⊗ E positive for every r, Tr E(X) = Tr X for all X; reason: every finite-dimensional auxiliary space is isomorphic to some ℂ^r; same notion
-- source:
--   Ben-David, Ebtehaj, Distributional Quantum Query Complexity, arXiv:2610.06835 (held version, sha256 6334ffaf…), §2.3.3, Theorem 2.5, p.16

import Mathlib
import Definitions.Def_WildeQIT_EntBreaking_IsQuantumChannel
import Definitions.Def_DistQuantumQuery_Supplement_schurChannel

open scoped Matrix ComplexOrder

namespace DistQuantumQuery.Supplement

/-- **Theorem 2.5** (Ben-David, Ebtehaj, *Distributional Quantum Query Complexity*,
arXiv:2610.06835, held version, sha256 6334ffaf…, Theorem 2.5, p.16). Let `G ∈ ℂ^{n×n}` be a Gram
matrix. Then the map `E_G : L(ℂ^n) → L(ℂ^n)` defined by `E_G(X) := X ∘ G^⊤` is a quantum channel.

**Formalization Note** "Gram matrix" is the page-16 notion, a Gram matrix corresponding to unit
vectors, which the page shows is the same as a positive semidefinite matrix with all diagonal
entries one; it is stated that way. A quantum channel is a linear, completely positive and trace
preserving map (§2.3.1, p.15), the published `WildeQIT.EntBreaking.IsQuantumChannel`. The index
set `[n]` is a finite type `n`. -/
theorem theorem_2_5 {n : Type} [Fintype n] [DecidableEq n] (G : Matrix n n ℂ)
    (hG : G.PosSemidef) (hdiag : ∀ i, G i i = 1) :
    WildeQIT.EntBreaking.IsQuantumChannel (schurChannel G) := by sorry

end DistQuantumQuery.Supplement
