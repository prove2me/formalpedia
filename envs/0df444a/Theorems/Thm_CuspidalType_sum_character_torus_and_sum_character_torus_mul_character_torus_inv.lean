-- Prove2me | Theorems.Thm_CuspidalType_sum_character_torus_and_sum_character_torus_mul_character_torus_inv
-- name    : CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/58e3a50e-f0fb-5540-a520-1caf08a7f4a0
-- title:
--   Elliptic character sums for a cuspidal-type representation of GL₂(𝔽_q)
-- statement:
--   Let $q$ be a prime, $K$ an algebraically closed field of characteristic zero, and $V$ a nonzero finite-dimensional $K$-vector space, and let $\rho$ be a representation of $G=\mathrm{GL}_2(\mathbb{Z}/q)$ on $V$, with character $\chi=\mathrm{tr}\,\rho$. Assume: $\dim_K V=q-1$ (truncated subtraction of naturals); $\chi(c\cdot g)=\chi(g)$ for every scalar matrix $c\cdot I$ with $c\in(\mathbb{Z}/q)^\times$ and every $g\in G$; $\chi\bigl(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\bigr)=-1$ for every $t\neq 0$; $\chi\bigl(\begin{smallmatrix}1&s\\0&1\end{smallmatrix}\bigr.\cdot\mathrm{diag}(a,1))=0$ for every $s\in\mathbb{Z}/q$ and every unit $a\neq 1$; $\sum_{g\in G}\chi(g)=0$; and $\sum_{g\in G}\chi(g)\chi(g^{-1})=|G|$ in $K$. Write $T\colon \mathbb{F}_{q^2}^\times\to G$ for the monoid homomorphism sending $\alpha$ to the matrix of multiplication by $\alpha$ on $\mathbb{F}_{q^2}=\mathrm{GaloisField}\ q\ 2$ in a fixed $\mathbb{Z}/q$-basis. The conclusion is the conjunction of two identities in $K$: $\sum_{\alpha\in\mathbb{F}_{q^2}^\times}\chi(T(\alpha))=q^2-1$ and $\sum_{\alpha\in\mathbb{F}_{q^2}^\times}\chi(T(\alpha))\,\chi(T(\alpha)^{-1})=(q-1)(q^2-1)$, both right-hand sides being natural numbers cast into $K$.
--
--   The hypotheses record the character values of a cuspidal representation of $\mathrm{GL}_2(\mathbb{F}_q)$ with trivial central character on the central, non-semisimple and split regular classes, together with the two orthogonality sums; the conclusion extracts the two corresponding sums over the non-split (elliptic) torus $\mathbb{F}_{q^2}^\times$. It feeds the analysis of the characteristic polynomials of torus elements in [`CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq`](thm.html#CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_sum_character_torus_and_sum_character_torus_mul_character_torus_inv.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.sum_character_torus_and_sum_character_torus_mul_character_torus_inv
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    [Fintype (GaloisField q 2)ˣ] (ρ : Representation K (GL2 q) V)
    (hK1 : Module.finrank K V = q - 1)
    (hK2 : ∀ (c : (ZMod q)ˣ) (g : GL2 q), ρ.character (scalarElem q c * g) = ρ.character g)
    (hK3 : ∀ t : ZMod q, t ≠ 0 → ρ.character (unipotent q t) = -1)
    (hK4 : ∀ (a : (ZMod q)ˣ) (s : ZMod q), a ≠ 1 → ρ.character (unipotent q s * diagElem q a) = 0)
    (hK5 : ∑ g : GL2 q, ρ.character g = 0)
    (hK6 : ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q)) :
    ∑ α : (GaloisField q 2)ˣ, ρ.character (torus q α) = ((q ^ 2 - 1 : ℕ) : K) ∧
    ∑ α : (GaloisField q 2)ˣ, ρ.character (torus q α) * ρ.character (torus q α)⁻¹ =
      (((q - 1) * (q ^ 2 - 1) : ℕ) : K) := by sorry
