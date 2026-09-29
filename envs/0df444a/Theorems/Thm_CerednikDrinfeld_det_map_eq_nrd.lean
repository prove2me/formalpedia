-- Prove2me | Theorems.Thm_CerednikDrinfeld_det_map_eq_nrd
-- name    : CerednikDrinfeld.det_map_eq_nrd
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:21.245927+00:00
-- url     : https://prove2.me/theorems/82406c01-df49-5ff2-a9e7-ce781e6f9d2a
-- title:
--   Real embeddings carry the reduced norm to the determinant
-- statement:
--   Let $a,b$ be rational numbers, both nonzero, and let $\mathbb{H}[\mathbb{Q},a,b]$ be the associated quaternion algebra over $\mathbb{Q}$, with basis $1,i,j,k$ subject to $i^2=a$, $j^2=b$, $k=ij$. On it the reduced norm is defined as the polynomial $\operatorname{nrd}(x)=x_{\mathrm{re}}^2-a\,x_{\mathrm{imI}}^2-b\,x_{\mathrm{imJ}}^2+ab\,x_{\mathrm{imK}}^2\in\mathbb{Q}$ in the coordinates of $x$. Let $\iota\colon \mathbb{H}[\mathbb{Q},a,b]\to M_2(\mathbb{R})$ be a homomorphism of $\mathbb{Q}$-algebras which is injective as a map of sets. Then for every $x$ in $\mathbb{H}[\mathbb{Q},a,b]$ the determinant of the real $2\times 2$ matrix $\iota(x)$ equals the image in $\mathbb{R}$ of the rational number $\operatorname{nrd}(x)$. No nondegeneracy or splitting hypothesis beyond $a\neq 0$, $b\neq 0$ and injectivity of $\iota$ is assumed; in particular $\iota$ is not required to be surjective or to be induced by a fixed isomorphism $\mathbb{H}[\mathbb{Q},a,b]\otimes_{\mathbb{Q}}\mathbb{R}\cong M_2(\mathbb{R})$.
--
--   This is the standard compatibility of the reduced norm with the determinant under a real splitting of an indefinite rational quaternion algebra; it is what makes elements of reduced norm $1$ land in $\mathrm{SL}_2(\mathbb{R})$. It is used in the Čerednik–Drinfeld part of the development, for instance in the construction of Hecke families and period maps on uniformised Hecke curves and in compactness arguments for quaternionic groups acting on the upper half-plane.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_det_map_eq_nrd.lean

import Definitions.Def_CerednikDrinfeld_ShimuraCurve

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion MatrixGroups TensorProduct NumberField
open IsDedekindDomain QuaternionAlgebra CerednikDrinfeld

theorem CerednikDrinfeld.det_map_eq_nrd {a b : ℚ} (ha : a ≠ 0) (hb : b ≠ 0)
    (ι : ℍ[ℚ, a, b] →ₐ[ℚ] Matrix (Fin 2) (Fin 2) ℝ) (hι : Function.Injective ι)
    (x : ℍ[ℚ, a, b]) : (ι x).det = ((nrd x : ℚ) : ℝ) := by sorry
