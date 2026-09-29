-- Prove2me | Theorems.Thm_AlgebraicCurve_ell_le_ell_sub_single_add_deg
-- name    : AlgebraicCurve.ell_le_ell_sub_single_add_deg
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:39.26765+00:00
-- url     : https://prove2.me/theorems/7225d5b1-f2eb-5f7d-ac68-bf454a2e9d73
-- title:
--   Single-place step: ℓ(D)≤ℓ(D-P)+deg P
-- statement:
--   Let $K$ and $F$ be fields with $F$ a $K$-algebra, and assume $F/K$ is a curve in the sense of the class `IsCurveOver`: every nonzero $f \in F$ admits a divisor whose value at each place $v$ is $v.\mathrm{ord}\,f$ and whose degree is $0$; each place has residue field finite over $K$; and the module of Kähler differentials $\Omega_{F/K}$ is free of rank one over $F$. Here a place of $F/K$ is a valuation subring of $F$ that contains the image of $K$, is not all of $F$, and is a principal ideal ring, and a divisor is a finitely supported function from places to $\mathbb{Z}$. Let $D$ be such a divisor and $P$ a place. Write $\ell(E)$ for the $K$-dimension (`Module.finrank`, hence $0$ if the space is not finite-dimensional) of the Riemann–Roch space of $E$, and $\deg P$ for the $K$-dimension of the residue field of the valuation subring of $P$. The assertion is the inequality $\ell(D) \le \ell(D - \delta_P) + \deg P$, where $\delta_P$ is the divisor taking the value $1$ at $P$ and $0$ elsewhere.
--
--   This is the elementary one-place step in the Riemann inequality for the dimensions of Riemann–Roch spaces, coming from the residue map $L(D) \to \kappa(P)$ whose kernel is $L(D-P)$. It is used in the project's estimates on dimensions of Riemann–Roch spaces, for instance in the results on finite-rank approximation under place reduction and in the torsion-descent statements for constant field extensions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicCurve_ell_le_ell_sub_single_add_deg.lean

import Mathlib
import Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Definitions.Def_AlgebraicCurve_Repartitions
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Definitions.Def_AlgebraicCurve_AdelicIndex

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace AlgebraicCurve

theorem ell_le_ell_sub_single_add_deg {K F : Type*} [Field K] [Field F] [Algebra K F] [IsCurveOver K F] (D : Divisor K F) (P : Place K F) :
    ell D ≤ ell (D - Finsupp.single P 1) + P.deg := by sorry
