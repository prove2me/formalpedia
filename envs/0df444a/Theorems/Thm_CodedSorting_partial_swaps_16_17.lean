-- Prove2me | Theorems.Thm_CodedSorting_partial_swaps_16_17
-- name    : CodedSorting.partial_swaps_16_17
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T23:06:28.188299+00:00
-- url     : https://prove2.me/theorems/8bca0b29-d1ec-4ad1-9073-c261de397953
-- title:
--   Displays (16)–(17) — partial swaps: $D_P^2=I$, $D_{P_V}D_{P_U}=D_{P_V-P_U}$, products, and $D_P=LT_{ij}L^{-1}$
-- statement:
--   Over $\mathbb Q$, let $D_P=\begin{pmatrix}I-P&P\\P&I-P\end{pmatrix}$ be the partial swap (16) of an $m\times m$ matrix $P$.
--
--   1. If $P^2=P$ then $D_P^2=I$. Moreover $D_0=I$ and $D_I(H,D)=(D,H)$.
--   2. If $U\subseteq V$ have orthogonal projections $P_U,P_V$, then $P_UP_V=P_VP_U=P_U$ and
--   $$D_{P_V}D_{P_U}=D_{P_U}D_{P_V}=D_{P_V-P_U}.$$
--   3. If $P_kP_l=0$ for all $k\ne l$, then $D_{P_1+\dots+P_r}=D_{P_1}D_{P_2}\cdots D_{P_r}$.
--   4. Let $u\in\mathbb Q^m$ be nonzero, $P=uu^{\mathsf T}/(u^{\mathsf T}u)$, $\xi=(u,-u)\in\mathbb Q^{2m}$, $\nu=\xi^{\mathsf T}\xi$, and let $i$ and $j$ be the indices of the first and last nonzero entries of $\xi$. Then $i$ lies in the first block and $j$ in the second, $D_P=I_{2m}-\frac2\nu\xi\xi^{\mathsf T}$, the matrix $L$ of p.22 is lower triangular with nonzero diagonal, and
--   $$D_PL=LT_{ij},\qquad D_P=LT_{ij}L^{-1},\tag{17}$$
--   where $T_{ij}$ is the permutation matrix exchanging coordinates $i$ and $j$.
--
--   These identities let a stream's storage order follow the circuit labels: a nested edge is one partial swap, a rank-$r$ partial swap is $r$ rank-one ones, and each rank-one partial swap is one short-field interchange between two triangular coordinate changes.
--
--   Differences from the source:
--   - generalization: pairwise orthogonal rank-one projections $P_k=u_ku_k^{\mathsf T}/(u_k^{\mathsf T}u_k)$ with $P_kP_l=0$ → any matrices with $P_kP_l=0$ for $k\ne l$; reason: the paper's projections satisfy the hypothesis (p.21), and its multiplication argument uses only it
--   - encoding: $2m\times2m$ matrices on $(H,D)$ → `Matrix (Fin m ⊕ Fin m)` for clauses 1–3 and `Fin (m+m)` (coordinates of $H$ first) for clause 4; reason: the same matrices
--   - encoding: $i$, $j$ the first and last nonzero entries of $\xi$ → hypotheses $\xi_i\ne0$, $\xi_k=0$ for $k<i$, $\xi_j\ne0$, $\xi_k=0$ for $k>j$; reason: these characterize $i$ and $j$ uniquely
-- source:
--   B. Li, Z. Li, S. Liu, Undirected Multiple-Unicast Network Coding and Faster External-Memory Integer Sorting, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §6.2, display (16) and the text after it, pp.20–21 (PDF 21–22), and display (17), p.22 (PDF 23)

import Mathlib
import Definitions.Def_CodedSorting_LinAlg

namespace CodedSorting

open Matrix

/-- **Partial swaps, displays (16)–(17)**, arXiv:2610.20079 (held version, sha256 6e149d97…8850b), §6.2, pp.20–22.

Over `ℚ`, with `D_P = psw P` the block matrix `[[I − P, P], [P, I − P]]` of (16):
1. if `P² = P` then `D_P² = I`; `D_0 = I` and `D_I(H, D) = (D, H)`;
2. if `U ⊆ V` have orthogonal projections `P_U`, `P_V`, then `P_U P_V = P_V P_U = P_U` and
   `D_{P_V} D_{P_U} = D_{P_U} D_{P_V} = D_{P_V − P_U}`;
3. if `P_k P_l = 0` for `k ≠ l`, then `D_{P_1 + ⋯ + P_r} = D_{P_1} D_{P_2} ⋯ D_{P_r}`;
4. for `u ≠ 0` in `ℚ^m` and `P = uuᵀ/(uᵀu)`, with `ξ = (u, −u) ∈ ℚ^{2m}`, `ν = ξᵀξ`, `i`, `j` the
   indices of the first and last nonzero entries of `ξ`: `i` lies in `H` and `j` in `D`,
   `D_P = I − (2/ν) ξξᵀ`, the matrix `L` of p.22 is lower triangular with nonzero diagonal, and
   `D_P L = L T_{ij}`, `D_P = L T_{ij} L⁻¹` (17), `T_{ij}` the permutation matrix exchanging
   coordinates `i` and `j`.

**Formalization Note.** In clause 4, `D_P` is written on `Fin (m + m)` (`pswFlat`), the coordinates
of `H` first. Clause 3 assumes only `P_k P_l = 0` for `k ≠ l`, which the paper's pairwise
orthogonal rank-one projections `P_k = u_k u_kᵀ/(u_kᵀu_k)` satisfy (p.21). -/
theorem partial_swaps_16_17 (m : ℕ) :
    (∀ P : Matrix (Fin m) (Fin m) ℚ, P * P = P → psw P * psw P = 1) ∧
    psw (0 : Matrix (Fin m) (Fin m) ℚ) = 1 ∧
    psw (1 : Matrix (Fin m) (Fin m) ℚ) = Matrix.fromBlocks 0 1 1 0 ∧
    (∀ (U V : Submodule ℚ (Fin m → ℚ)) (P Q : Matrix (Fin m) (Fin m) ℚ),
      IsOrthProj U P → IsOrthProj V Q → U ≤ V →
        P * Q = P ∧ Q * P = P ∧ psw Q * psw P = psw (Q - P) ∧ psw P * psw Q = psw (Q - P)) ∧
    (∀ (r : ℕ) (Ps : Fin r → Matrix (Fin m) (Fin m) ℚ), (∀ k l, k ≠ l → Ps k * Ps l = 0) →
      psw (∑ k, Ps k) = (List.ofFn (fun k => psw (Ps k))).prod) ∧
    (∀ (u : Fin m → ℚ) (i j : Fin (m + m)), u ≠ 0 →
      Fin.append u (-u) i ≠ 0 → (∀ k, k < i → Fin.append u (-u) k = 0) →
      Fin.append u (-u) j ≠ 0 → (∀ k, j < k → Fin.append u (-u) k = 0) →
      (i : ℕ) < m ∧ m ≤ (j : ℕ) ∧
      pswFlat ((u ⬝ᵥ u)⁻¹ • vecMulVec u u) =
        1 - (2 / (Fin.append u (-u) ⬝ᵥ Fin.append u (-u))) •
          vecMulVec (Fin.append u (-u)) (Fin.append u (-u)) ∧
      (∀ a b, a < b → lowerL (Fin.append u (-u)) i j a b = 0) ∧
      (∀ a, lowerL (Fin.append u (-u)) i j a a ≠ 0) ∧
      pswFlat ((u ⬝ᵥ u)⁻¹ • vecMulVec u u) * lowerL (Fin.append u (-u)) i j =
        lowerL (Fin.append u (-u)) i j * (Equiv.swap i j).permMatrix ℚ ∧
      pswFlat ((u ⬝ᵥ u)⁻¹ • vecMulVec u u) =
        lowerL (Fin.append u (-u)) i j * (Equiv.swap i j).permMatrix ℚ *
          (lowerL (Fin.append u (-u)) i j)⁻¹) := by sorry

end CodedSorting
