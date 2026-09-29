-- Prove2me | Theorems.Thm_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero
-- name    : Deformation.mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:39.646648+00:00
-- url     : https://prove2.me/theorems/867a8107-5548-519f-8c98-8de1c21669fd
-- title:
--   Primitivity criterion for Witt vectors concentrated in the last coordinate
-- statement:
--   Let $R$ be a commutative ring, $p$ a prime, $n$ a natural number, and let $A$ be a commutative ring carrying an $R$-bialgebra structure. Let $x$ be a truncated Witt vector of length $n+1$ with entries in $A$, and suppose that $x.\mathrm{coeff}\,i = 0$ for every $i \in \mathrm{Fin}(n+1)$ with $i \neq \mathrm{Fin.last}\,n$, i.e. all coordinates of $x$ except the last vanish. The assertion is that $x$ lies in the additive subgroup [`Deformation.wittHom R p (n+1) A`](def/Dieudonne_WittVectorHom.html#L246) of $\mathrm{W}_{n+1}(A)$ — by definition, the set of those $x$ for which the functorial map on truncated Witt vectors induced by the comultiplication ring homomorphism $A \to A \otimes_R A$ sends $x$ to the sum of the images of $x$ under the maps induced by the two algebra inclusions $a \mapsto a \otimes 1$ and $a \mapsto 1 \otimes a$ — if and only if the last coordinate is primitive, i.e. $\Delta(x.\mathrm{coeff}(\mathrm{Fin.last}\,n)) = x.\mathrm{coeff}(\mathrm{Fin.last}\,n) \otimes 1 + 1 \otimes x.\mathrm{coeff}(\mathrm{Fin.last}\,n)$ in $A \otimes_R A$.
--
--   With $G = \operatorname{Spec} A$, membership in [`Deformation.wittHom`](def/Dieudonne_WittVectorHom.html#L246) expresses that $x$ is a homomorphism of group schemes $G \to \mathrm{W}_{n+1}$, so this identifies the kernel of the restriction $\operatorname{Hom}(G, \mathrm{W}_{n+1}) \to \operatorname{Hom}(G, \mathrm{W}_n)$ with the group of primitive elements $\operatorname{Hom}(G, \mathbb{G}_a)$, via the last coordinate. It is the dévissage step used in the surjectivity statement [`HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero`](thm.html#HopfAlgebra.wittHomMap_surjective_of_surjective_of_forall_convPow_eq_zero) for the Dieudonné-module computations.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero.lean

import Mathlib
import Definitions.Def_Dieudonne_DatumAndHonda
import Definitions.Def_Dieudonne_WittVectorHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v

theorem Deformation.mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A]
    (x : TruncatedWittVector p (n + 1) A)
    (hx : ∀ i : Fin (n + 1), i ≠ Fin.last n → x.coeff i = 0) :
    x ∈ Deformation.wittHom R p (n + 1) A ↔
      Coalgebra.comul (R := R) (x.coeff (Fin.last n)) =
        x.coeff (Fin.last n) ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] x.coeff (Fin.last n) := by sorry
