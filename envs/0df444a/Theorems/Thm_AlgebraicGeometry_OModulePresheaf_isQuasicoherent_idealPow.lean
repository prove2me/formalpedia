-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPow
-- name    : AlgebraicGeometry.OModulePresheaf.isQuasicoherent_idealPow
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/2868960b-6385-5e08-b809-976029c9c78d
-- title:
--   Quasi-coherence of the ideal-power subdatum I^k F
-- statement:
--   Let $R$ be a commutative ring, let $V$ be a scheme and let $\pi \colon V \to \operatorname{Spec} R$ be a morphism, which makes each $\Gamma(V,U)$ an $R$-algebra via `algebraOfHom`. Let $I$ be an ideal sheaf datum on $V$, let $F$ be an `OModulePresheaf` over $\pi$ — that is, an assignment $U \mapsto F(U)$ of $R$-modules to the opens of $V$, each also a $\Gamma(V,U)$-module compatibly with the $R$-action, together with $R$-linear restriction maps $F(U') \to F(U)$ for $U \le U'$ that are semilinear for the restriction of sections, reflexive and functorial — and let $k$ be a natural number. Assume $F$ is quasi-coherent in the sense of `IsQuasicoherent`: for every affine open $U$ of $V$ and every $f \in \Gamma(V,U)$, first, every $x \in F(D(f))$ satisfies $\rho(f^n)\cdot x = \mathrm{res}(y)$ for some $n \in \mathbb N$ and some $y \in F(U)$, where $\rho$ denotes restriction of sections to the basic open $D(f)$, and second, every $y \in F(U)$ restricting to $0$ in $F(D(f))$ is annihilated by $f^n$ for some $n$. The conclusion is that the subdatum `idealPow` $\pi$ $I$ $F$ $k$ is quasi-coherent in the same sense; here `idealPow` assigns to $U$ the $R$-submodule obtained by restricting scalars from the $\Gamma(V,U)$-submodule $J_U^k \cdot F(U)$ of $F(U)$, where $J_U$ is the kernel of the map $\Gamma(V,U) \to \Gamma(\text{closed subscheme of } I, U)$ induced by $I$, with restriction maps induced by those of $F$.
--
--   This is the quasi-coherence of the terms of the $I$-adic filtration $F \supseteq \mathcal I F \supseteq \mathcal I^2 F \supseteq \cdots$ of a quasi-coherent module-presheaf datum, formulated in the elementary 'basic open' form of quasi-coherence over an affine open. It feeds the reduction of statements about data supported in a closed subscheme to data annihilated by its ideal, and is cited by [`AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates`](thm.html#AlgebraicGeometry.OModulePresheaf.forall_of_forall_idealAnnihilates).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_isQuasicoherent_idealPow.lean

import Mathlib.AlgebraicGeometry.Morphisms.Separated
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.Localization.Away.Basic
import Definitions.Def_AlgebraicGeometry_OModulePresheafIdealFiltration

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.isQuasicoherent_idealPow {R : Type u} [CommRing R] {V : Scheme.{u}} (π : V ⟶ Spec (.of R)) (I : V.IdealSheafData) (F : OModulePresheaf π) (k : ℕ) (hFq : F.IsQuasicoherent) : (OModulePresheaf.idealPow π I F k).IsQuasicoherent := by sorry
