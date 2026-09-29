-- Prove2me | Theorems.Thm_CerednikDrinfeld_exists_isCompact_finset_forall_sl
-- name    : CerednikDrinfeld.exists_isCompact_finset_forall_sl
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:26.413891+00:00
-- url     : https://prove2.me/theorems/dcdac370-413e-5aff-a4cd-a57e54e9fb47
-- title:
--   Minkowski step for orders in an indefinite quaternion algebra
-- statement:
--   Let $a,b\in\mathbb{Q}$ and let $\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra over $\mathbb{Q}$. Assume that every nonzero element of $\mathbb{H}[\mathbb{Q},a,b]$ is a unit, so that the algebra is a division algebra. Let $R$ be a $\mathbb{Z}$-submodule of $\mathbb{H}[\mathbb{Q},a,b]$ which is an order in the sense of the predicate `IsOrder`: $1\in R$, $R$ is closed under multiplication, the $\mathbb{Q}$-span of $R$ is all of $\mathbb{H}[\mathbb{Q},a,b]$, and $R$ is finitely generated as a $\mathbb{Z}$-module. Let $\iota\colon \mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ be an injective homomorphism of $\mathbb{Q}$-algebras. Then there exist a set $C\subseteq M_2(\mathbb{R})$ and a finite set $S$ of rational numbers such that $C$ is compact and, for every $g\in \mathrm{SL}_2(\mathbb{R})$, there is an $r\in R$ with $r\neq 0$, with reduced norm $\mathrm{nrd}(r)=r_{\mathrm{re}}^2-a\,r_{I}^2-b\,r_{J}^2+ab\,r_{K}^2$ lying in $S$, and with $\iota(r)\cdot g\in C$. The compact set and the finite set of norms are chosen once and for all, uniformly in $g$.
--
--   This is the Minkowski-type step in the classical argument that the unit group of an order in an indefinite division quaternion algebra over $\mathbb{Q}$ acts cocompactly on the upper half-plane: the image $\iota(R)$ is a full lattice in $M_2(\mathbb{R})\cong\mathbb{R}^4$, right translation by an element of determinant $1$ preserves volume, and the reduced norms of lattice points in a fixed bounded set form a finite set of rationals. It is used by [`CerednikDrinfeld.exists_isCompact_forall_exists_fuchsianGroup_smul_mem`](thm.html#CerednikDrinfeld.exists_isCompact_forall_exists_fuchsianGroup_smul_mem), the cocompactness statement for the associated Fuchsian group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_exists_isCompact_finset_forall_sl.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.exists_isCompact_finset_forall_sl {a b : ℚ}
    (hdiv : ∀ x : ℍ[ℚ, a, b], x ≠ 0 → IsUnit x)
    (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι) :
    ∃ (C : Set (Matrix (Fin 2) (Fin 2) ℝ)) (S : Finset ℚ), IsCompact C ∧
      ∀ g : Matrix.SpecialLinearGroup (Fin 2) ℝ, ∃ r ∈ R, r ≠ 0 ∧ nrd r ∈ S ∧
        ι r * (g : Matrix (Fin 2) (Fin 2) ℝ) ∈ C := by sorry
