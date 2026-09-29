-- Prove2me | Theorems.Thm_CerednikDrinfeld_apply_apply_sub_apply_add_smul_eq_zero_of_reduction
-- name    : CerednikDrinfeld.apply_apply_sub_apply_add_smul_eq_zero_of_reduction
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/457322ed-8955-50b0-9ebf-fb951f0979c6
-- title:
--   Algebraic core of the Eichler–Shimura congruence relation
-- statement:
--   Let $J$ and $P$ be additive abelian groups, $D \le J$ a subgroup, and $g, T : J \to J$ arbitrary maps (no additivity is assumed) which send $D$ into $D$. Let $\mathrm{red} : J \to P$ be a map that is additive on $D$, in the sense that $\mathrm{red}(x+y) = \mathrm{red}\,x + \mathrm{red}\,y$ for all $x, y \in D$, and injective on $D$ in the sense that $x \in D$ and $\mathrm{red}\,x = 0$ force $x = 0$. Let $F, V : P \to P$ be endomorphisms of the additive group $P$ and let $\ell$ be a natural number, subject to three conditions valid for every $t \in D$: $\mathrm{red}(g\,t) = F(\mathrm{red}\,t)$, $\mathrm{red}(T\,t) = F(\mathrm{red}\,t) + V(\mathrm{red}\,t)$, and $V(F(\mathrm{red}\,t)) = \ell \cdot \mathrm{red}\,t$. The conclusion is that $g(g\,t) - T(g\,t) + \ell \cdot t = 0$ in $J$ for every $t \in D$, the scalar multiple being the $\mathbb{N}$-action on the abelian group $J$.
--
--   This is the purely group-theoretic skeleton of the Eichler–Shimura congruence relation $\mathrm{Frob}^2 - T_\ell\,\mathrm{Frob} + \ell = 0$: in the intended application $J$ is the group of degree-zero divisor classes of a curve over $\overline{\mathbb{Q}}$, $D$ its $p$-torsion, $g$ a Frobenius element at a place above $\ell$, $T$ the Hecke operator $T_\ell$, $\mathrm{red}$ reduction to the special fibre, and $F$, $V$ the Frobenius and Verschiebung there. It is used by [`CerednikDrinfeld.ShimuraCurveModel.eichlerShimura_of_rigidModuliWitness_of_two_mul_dvd`](thm.html#CerednikDrinfeld.ShimuraCurveModel.eichlerShimura_of_rigidModuliWitness_of_two_mul_dvd) to transport the congruence relation from the special fibre to the characteristic-zero Picard group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_apply_apply_sub_apply_add_smul_eq_zero_of_reduction.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem CerednikDrinfeld.apply_apply_sub_apply_add_smul_eq_zero_of_reduction
    {J P : Type*} [AddCommGroup J] [AddCommGroup P]
    (D : AddSubgroup J) (g T : J → J) (hg : ∀ t ∈ D, g t ∈ D) (hT : ∀ t ∈ D, T t ∈ D)
    (red : J → P) (hadd : ∀ x ∈ D, ∀ y ∈ D, red (x + y) = red x + red y)
    (hinj : ∀ x ∈ D, red x = 0 → x = 0)
    (F V : P →+ P) (ℓ : ℕ)
    (hgal : ∀ t ∈ D, red (g t) = F (red t))
    (hhecke : ∀ t ∈ D, red (T t) = F (red t) + V (red t))
    (hVF : ∀ t ∈ D, V (F (red t)) = ℓ • red t) :
    ∀ t ∈ D, g (g t) - T (g t) + ℓ • t = 0 := by sorry
