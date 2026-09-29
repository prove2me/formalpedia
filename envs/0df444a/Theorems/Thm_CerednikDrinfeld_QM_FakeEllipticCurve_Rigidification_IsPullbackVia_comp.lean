-- Prove2me | Theorems.Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_IsPullbackVia_comp
-- name    : CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.IsPullbackVia.comp
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:00.242033+00:00
-- url     : https://prove2.me/theorems/5f117774-012b-50b6-a00e-a9d4f71caf85
-- title:
--   Composition of pull-backs of rigidifications
-- statement:
--   Fix natural numbers $r$ and $N$, a commutative ring $\mathcal O$ with an element $\pi$, an $\mathcal O$-algebra $O^{nr}$, rationals $a,b$ and a $\mathbb Z$-submodule $\Lambda$ of the quaternion algebra $\mathbb H[\mathbb Q,a,b]$, together with a fake elliptic curve $A_0$ of level $N$ with $\Lambda$-action over $O^{nr}/(\pi)$. Let $\varphi : B \to B'$ and $\varphi' : B' \to B''$ be morphisms of $\mathcal O$-algebras, $\psi : O^{nr} \to B$ an $\mathcal O$-algebra map, and $E,E',E''$ fake elliptic curves for $(\Lambda,N)$ over $B,B',B''$. Let $g : E'.A \to E.A$ and $g' : E''.A \to E'.A$ be scheme morphisms, with hypotheses `FakeEllipticCurve.IsPullbackVia` for $g$ along $\varphi$, for $g'$ along $\varphi'$, and for $g'$ followed by $g$ along $\varphi' \circ \varphi$; each such hypothesis says that the square over $\mathrm{Spec}$ of the ring map is a pullback, that $g$ is compatible with the relative group laws on $T$-points, commutes with the $\Lambda$-actions, and carries points factoring through the level structure of the source into points factoring through that of the target. Let $\rho$, $\rho'$, $\rho''$ be rigidifications (in the sense of the structure `FakeEllipticCurve.Rigidification` for $r$, $\pi$, $A_0$) of $E$, $E'$, $E''$ along the legs $\psi$, $\varphi \circ \psi$, $\varphi' \circ \varphi \circ \psi$. Assume $\rho'$ is the pull-back of $\rho$ along $\varphi$ via $g$ and $\rho''$ the pull-back of $\rho'$ along $\varphi'$ via $g'$. Then $\rho''$ is the pull-back of $\rho$ along $\varphi' \circ \varphi$ via $g'$ followed by $g$: there are morphisms $u_b : \rho''.Eb.A \to \rho.Eb.A$ and $u_A : \rho''.Ab.A \to \rho.Ab.A$ exhibiting the mod-$\pi$ reductions $\rho''.Eb$, $\rho''.Ab$ as pull-backs of $\rho.Eb$, $\rho.Ab$ along the map $B/(\pi) \to B''/(\pi)$ induced by $\varphi' \circ \varphi$, compatible with the comparison maps to $E.A$ and to $A_0.A$, with $\rho''.d = \rho.d$ and $u_b$ followed by $\rho.\varphi$ equal to $\rho''.\varphi$ followed by $u_A$. The composite pull-back hypothesis for $g'$ followed by $g$ is a datum needed to state the conclusion; the defining conditions of the conclusion do not refer to it.
--
--   This is the transitivity (cocycle) statement for base change of rigidifications of fake elliptic curves along a composable pair of $\mathcal O$-algebra maps, the rigidification-level counterpart of the corresponding statement for the underlying fake elliptic curves. It is used when rigidified families are glued or transported along covers, for instance in the construction of naturality for rigidified families and in statements about fine level structures in the Čerednik–Drinfeld setting.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_CerednikDrinfeld_QM_FakeEllipticCurve_Rigidification_IsPullbackVia_comp.lean

import Definitions.Def_CerednikDrinfeld_QMRigidification

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open scoped Quaternion
open CategoryTheory AlgebraicGeometry CerednikDrinfeld.QM

theorem CerednikDrinfeld.QM.FakeEllipticCurve.Rigidification.IsPullbackVia.comp
    {r N : ℕ} {𝒪 : Type} [CommRing 𝒪] {π : 𝒪} {Onr : Type} [CommRing Onr] [Algebra 𝒪 Onr]
    {a b : ℚ} {Λ : Submodule ℤ ℍ[ℚ, a, b]} {A₀ : FakeEllipticCurve Λ N (Onr ⧸ Ideal.span {algebraMap 𝒪 Onr π})}
    {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B'] {B'' : Type} [CommRing B''] [Algebra 𝒪 B'']
    (φ : B →ₐ[𝒪] B') (φ' : B' →ₐ[𝒪] B'') {ψ : Onr →ₐ[𝒪] B}
    {E : FakeEllipticCurve Λ N B} {E' : FakeEllipticCurve Λ N B'} {E'' : FakeEllipticCurve Λ N B''}
    (g : E'.A ⟶ E.A) (hg : FakeEllipticCurve.IsPullbackVia (φ : B →+* B') E E' g)
    (g' : E''.A ⟶ E'.A) (hg' : FakeEllipticCurve.IsPullbackVia (φ' : B' →+* B'') E' E'' g')
    (hgg : FakeEllipticCurve.IsPullbackVia ((φ'.comp φ : B →ₐ[𝒪] B'') : B →+* B'') E E'' (g' ≫ g))
    (ρ : FakeEllipticCurve.Rigidification r π A₀ ψ E) (ρ' : FakeEllipticCurve.Rigidification r π A₀ (φ.comp ψ) E')
    (ρ'' : FakeEllipticCurve.Rigidification r π A₀ (φ'.comp (φ.comp ψ)) E'')
    (h : FakeEllipticCurve.Rigidification.IsPullbackVia φ g hg ρ ρ')
    (h' : FakeEllipticCurve.Rigidification.IsPullbackVia φ' g' hg' ρ' ρ'') :
    FakeEllipticCurve.Rigidification.IsPullbackVia (φ'.comp φ) (g' ≫ g) hgg ρ ρ'' := by sorry
