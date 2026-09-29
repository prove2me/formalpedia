-- Prove2me | Theorems.Thm_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_of_chain
-- name    : CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_of_chain
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:59.785899+00:00
-- url     : https://prove2.me/theorems/d1500b7c-a236-5039-b2b4-2c5f36511252
-- title:
--   Gluing holomorphy along a chain of pieces
-- statement:
--   Let $K$ be an algebraically closed field carrying a valuation $v =$ `Valued.v` with values in a linearly ordered commutative group with zero $\Gamma_0$, let $S \subseteq K$ be a set, let $k$ be a natural number and let $P_0, \dots, P_k \subseteq K$ be sets with $P_j \subseteq S$ for all $j$ and $S \subseteq \bigcup_j P_j$. Let $t, \pi : \mathrm{Fin}(k+1) \to K$ and let $Z_j$ be finite subsets of $K$, subject to: $\pi_j \neq 0$ for every $j \neq 0$; for $j \neq 0$ and $i < j$, every $z \in P_i$ satisfies $v(\pi_j) \le v(z - t_j)$; for $j \neq 0$, every $z \in P_j$ either lies in some $P_i$ with $i < j$ or satisfies $v(z - t_j) < v(\pi_j)$; and for $j \neq 0$, every $z \in K$ with $v(z - t_j) = v(\pi_j)$ and $v(\pi_j) \le v(z - \zeta)$ for all $\zeta \in Z_j$ lies in $P_j$ and also in some $P_i$ with $i < j$. Let $h : S \to K$ be a function whose restriction to each $P_j$ lies in `holOn K (P j)`, that is, is the uniform limit of a sequence of rational pairs which are pole-free on $P_j$ and whose values on $P_j$ are bounded in absolute value uniformly in the index. Then $h$ itself lies in `holOn K S`: there is a sequence of rational pairs, pole-free on $S$, with values uniformly bounded on $S$, converging to $h$ uniformly on $S$.
--
--   This is the finite-chain form of the sheaf property for rigid-analytic functions in the shape used here: holomorphy on a finite cover whose pieces are attached one at a time across a sphere $v(z - t_j) = v(\pi_j)$, away from finitely many residue discs about $Z_j$, implies holomorphy on the union. It is used in the construction of holomorphic functions on the affinoids of Drinfeld's upper half-plane, via `exists_holOn_affinoid_mul_pullback_eq_of_cover_clearing_of_cerednikDrinfeld_quotient`, where the pieces are the edge regions of a ball in the Bruhat–Tits tree enumerated outward from the centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_Omega_mem_holOn_of_forall_mem_holOn_of_chain.lean

import Definitions.Def_CerednikDrinfeld_DrinfeldHolomorphic
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CerednikDrinfeld.Omega

theorem CerednikDrinfeld.Omega.mem_holOn_of_forall_mem_holOn_of_chain
    (K : Type) [Field K] {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀] [IsAlgClosed K]
    (S : Set K) (k : ℕ) (P : Fin (k + 1) → Set K)
    (hsub : ∀ j, P j ⊆ S) (hcov : S ⊆ ⋃ j, P j)
    (t π : Fin (k + 1) → K) (Z : Fin (k + 1) → Finset K)
    (hπ : ∀ j, j ≠ 0 → π j ≠ 0)
    (hout : ∀ j, j ≠ 0 → ∀ i, i < j → ∀ z ∈ P i, Valued.v (π j) ≤ Valued.v (z - t j))
    (hin : ∀ j, j ≠ 0 → ∀ z ∈ P j, (∃ i, i < j ∧ z ∈ P i) ∨ Valued.v (z - t j) < Valued.v (π j))
    (hrim : ∀ j, j ≠ 0 → ∀ z : K, Valued.v (z - t j) = Valued.v (π j) →
      (∀ ζ ∈ Z j, Valued.v (π j) ≤ Valued.v (z - ζ)) → z ∈ P j ∧ ∃ i, i < j ∧ z ∈ P i)
    (h : ↥S → K)
    (hh : ∀ j, (fun z : ↥(P j) => h ⟨(z : K), hsub j z.2⟩) ∈ holOn K (P j)) :
    h ∈ holOn K S := by sorry
