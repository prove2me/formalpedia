-- Prove2me | Theorems.Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_oSub_of_mem_support_ohom
-- name    : AlgebraicGeometry.Scheme.OrderedAffineCover.oSub_of_mem_support_ohom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:48.067734+00:00
-- url     : https://prove2.me/theorems/1454af69-1089-51ff-9b8d-88b5f11a6590
-- title:
--   Entries of the homotopy's support come from σ
-- statement:
--   Let $V$ be a scheme and let $K$ be an ordered affine cover of $V$, that is, a finite linearly ordered index type $\iota$ together with opens $U_i \subseteq V$, each affine, whose supremum is $\top$. Fix $n \in \mathbb{N}$, an ordered index tuple $\sigma : \mathrm{Fin}(n+1) \to \iota$ (an element of `K.OIdx n`) and a tuple $u : \mathrm{Fin}(n+2) \to \iota$ (an element of `K.OIdx (n+1)`). The hypothesis is that $u$ lies in the support of the chain `K.ohom n σ`, an element of `K.OCh (n+1)`, i.e. the coefficient of $u$ in that finitely supported $\mathbb{Z}$-valued function on `K.OIdx (n+1)` is nonzero; here `ohom` is defined by recursion, vanishing for $n = 0$ and sending $\sigma$ in degree $n+1$ to the cone on $\sigma(0)$ applied to $\delta_\sigma$ minus its ordered-sorting image `oesort` minus the image under `olin n (ohom n)` of the boundary `obd n` of $\delta_\sigma$. The conclusion is `K.OSub u σ`: for every index $j$ there is an index $i$ with $u(j) = \sigma(i)$, i.e. every entry of $u$ occurs among the entries of $\sigma$.
--
--   This is the carrier estimate for the acyclic-carriers homotopy between the alternating and ordered Čech complexes of an ordered affine cover: the homotopy applied to $\sigma$ is supported on tuples drawn from the entries of $\sigma$. It is what makes pairing a cochain against `K.ohom n σ` legitimate, since the restriction maps out of $U_u$ into $U_\sigma$ exist precisely when $u$ is drawn from $\sigma$; it is used in [`AlgebraicGeometry.OModulePresheaf.sub_oext_ores_mem_of_od_eq_zero`](thm.html#AlgebraicGeometry.OModulePresheaf.sub_oext_ores_mem_of_od_eq_zero).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_Scheme_OrderedAffineCover_oSub_of_mem_support_ohom.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCech
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechCup
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCochainPullback
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrdered
import Definitions.Def_AlgebraicGeometry_OrderedAffineCoverCechOrderedChains

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

theorem AlgebraicGeometry.Scheme.OrderedAffineCover.oSub_of_mem_support_ohom
    {V : Scheme.{u}} (K : V.OrderedAffineCover) (n : ℕ) (σ : K.OIdx n) (u : K.OIdx (n + 1))
    (hu : u ∈ (K.ohom n σ).support) : K.OSub u σ := by sorry
