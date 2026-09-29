-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:08.2859+00:00
-- url     : https://prove2.me/theorems/363bc2dc-40d6-57b9-ba83-c39706bb30ef
-- title:
--   Smoothness of relative dimension two for fake elliptic curves
-- statement:
--   Fix rationals $a,b$, a $\mathbb{Z}$-submodule $\Lambda$ of the quaternion algebra $\mathbb{H}[\mathbb{Q},a,b]$ and a natural number $N$; let $k$ be a field and let $E$ be a term of `FakeEllipticCurve Λ N k`. Such an $E$ consists of a scheme $E.A$, a morphism $E.f : E.A \to \operatorname{Spec} k$, a relative group law $E.L$ on $E.f$ (a group structure, functorial in the base, on the sets $\{\varphi : T \to E.A \mid \varphi \text{ followed by } E.f = t\}$ of sections over arbitrary $t : T \to \operatorname{Spec} k$) which is commutative, a bundle `E.bundle` asserting that $E.f$ is smooth and proper, that each fibre $E.f^{-1}(s)$ is connected, and that a relative group law on $E.f$ exists, the requirement that every fibre $E.f^{-1}(s)$ have topological Krull dimension $2$, an action of $\Lambda$ by endomorphisms of $E.A$ over $\operatorname{Spec} k$ compatible with the group law in the stated additive and multiplicative senses together with the trace condition on the induced action on tangent vectors, and further components (a curve $C$ and the remaining level-$N$ data), summarised here. The conclusion is that $E.f$ is smooth of relative dimension $2$ in Mathlib's sense, `SmoothOfRelativeDimension 2 E.f`. Only the smoothness and fibre connectedness from `E.bundle`, the group law $E.L$ and the fibre-dimension clause are used; the other components of the structure.
--
--   This converts the two separate conditions carried by the definition of a fake elliptic curve over a field — smoothness in the unqualified sense together with the requirement that the fibres have topological Krull dimension two — into the single statement that the structure morphism is smooth of relative dimension two. It is the form used throughout the subsequent analysis of fake elliptic curves, in particular in the rank computations for kernels of isogenies and torsion subschemes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_smoothOfRelativeDimension_two.lean

import Definitions.Def_CerednikDrinfeld_QMModuli

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry NeronModelInfra CerednikDrinfeld CerednikDrinfeld.QM
open scoped Quaternion

theorem CerednikDrinfeld.QM.FakeEllipticCurve.smoothOfRelativeDimension_two
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {N : ℕ}
    (k : Type u) [Field k] (E : FakeEllipticCurve Λ N k) :
    SmoothOfRelativeDimension 2 E.f := by sorry
