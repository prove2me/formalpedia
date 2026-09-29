-- Prove2me | Theorems.Thm_CuspidalType_exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq
-- name    : CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/0adc60a2-4176-599e-8b81-d8f52406419e
-- title:
--   Torus charpoly of a cuspidal-type character: ρ|_T = bigoplus_μ ≠ θ,θ⁻¹μ
-- statement:
--   Let $q$ be a prime, $K$ an algebraically closed field of characteristic zero, and $V$ a non-trivial finite-dimensional $K$-vector space, and let $\rho$ be a $K$-linear representation of $\mathrm{GL}_2(\mathbb{Z}/q)$ on $V$. Assume: $\rho$ sends every scalar matrix $c\cdot I$, $c\in(\mathbb{Z}/q)^\times$, to the identity; $\dim_K V = q-1$ (truncated subtraction of naturals); the character $\chi=\mathrm{tr}\,\rho$ satisfies $\chi(c\cdot I\cdot g)=\chi(g)$ for all scalars $c$ and all $g$; $\chi\bigl(\begin{smallmatrix}1&t\\0&1\end{smallmatrix}\bigr)=-1$ for every $t\neq 0$; $\chi\bigl(\begin{smallmatrix}1&s\\0&1\end{smallmatrix}\bigr.\bigl(\begin{smallmatrix}a&0\\0&1\end{smallmatrix}\bigr)=0$ for every $s$ and every unit $a\neq 1$; $\sum_{g}\chi(g)=0$; and $\sum_g \chi(g)\chi(g^{-1})=|\mathrm{GL}_2(\mathbb{Z}/q)|$. Let $S_0$ be a finite set of group homomorphisms $\mathbb{F}_{q^2}^\times\to K^\times$ consisting exactly of those that are trivial on the image of $(\mathbb{Z}/q)^\times$ under the inclusion $\mathbb{Z}/q\hookrightarrow\mathbb{F}_{q^2}$. The conclusion is that there exists $\theta\in S_0$ with $\theta^2\neq 1$ such that for every $\alpha\in\mathbb{F}_{q^2}^\times$, writing $T(\alpha)\in\mathrm{GL}_2(\mathbb{Z}/q)$ for the matrix of multiplication by $\alpha$ on $\mathbb{F}_{q^2}$ in a fixed $\mathbb{Z}/q$-basis, $$\det\bigl(X-\rho(T(\alpha))\bigr)\cdot\bigl(X-\theta(\alpha)\bigr)\bigl(X-\theta(\alpha)^{-1}\bigr)=\prod_{\mu\in S_0}\bigl(X-\mu(\alpha)\bigr).$$
--
--   This is the torus-side step in the classification of cuspidal representations of $\mathrm{GL}_2(\mathbb{F}_q)$ with trivial central character: the stated character identities force the restriction of $\rho$ to the non-split torus $\mathbb{F}_{q^2}^\times$ to be the sum of all characters trivial on $\mathbb{F}_q^\times$ except for a Frobenius-conjugate pair $\theta,\theta^{-1}=\theta^q$ with $\theta^2\neq 1$, which is the datum of a cuspidal type $\theta$. It is used in the construction of the cuspidal type attached to an irreducible cuspidal representation with trivial centre.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CuspidalType_exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq.lean

import Mathlib
import Definitions.Def_CuspidalType_IsCuspidalOfType

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open Polynomial CuspidalType

theorem CuspidalType.exists_sq_ne_one_and_forall_charpoly_torus_mul_eq_prod_of_forall_character_eq
    {q : ℕ} [Fact q.Prime] {K : Type*} [Field K] [IsAlgClosed K] [CharZero K]
    {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Nontrivial V]
    (ρ : Representation K (GL2 q) V)
    (hcent : ∀ c : (ZMod q)ˣ, ρ (scalarElem q c) = LinearMap.id)
    (hK1 : Module.finrank K V = q - 1)
    (hK2 : ∀ (c : (ZMod q)ˣ) (g : GL2 q), ρ.character (scalarElem q c * g) = ρ.character g)
    (hK3 : ∀ t : ZMod q, t ≠ 0 → ρ.character (unipotent q t) = -1)
    (hK4 : ∀ (a : (ZMod q)ˣ) (s : ZMod q), a ≠ 1 → ρ.character (unipotent q s * diagElem q a) = 0)
    (hK5 : ∑ g : GL2 q, ρ.character g = 0)
    (hK6 : ∑ g : GL2 q, ρ.character g * ρ.character g⁻¹ = Nat.card (GL2 q))
    (S₀ : Finset ((GaloisField q 2)ˣ →* Kˣ)) (hS₀ : ∀ μ : (GaloisField q 2)ˣ →* Kˣ,
      μ ∈ S₀ ↔ ∀ c : (ZMod q)ˣ, μ (Units.map (algebraMap (ZMod q) (GaloisField q 2)).toMonoidHom c) = 1) :
    ∃ θ ∈ S₀, θ ^ 2 ≠ 1 ∧ ∀ α : (GaloisField q 2)ˣ,
      (ρ (torus q α)).charpoly * ((X - C ((θ α : Kˣ) : K)) * (X - C (((θ α)⁻¹ : Kˣ) : K))) =
        ∏ μ ∈ S₀, (X - C ((μ α : Kˣ) : K)) := by sorry
