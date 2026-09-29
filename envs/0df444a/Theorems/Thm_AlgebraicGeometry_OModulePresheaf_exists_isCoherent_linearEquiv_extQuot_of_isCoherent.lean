-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent
-- name    : AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_extQuot_of_isCoherent
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/c5f78790-6be2-5cbc-97c4-789ffbf5c178
-- title:
--   A coherent datum computing local Ext¹ of two coherent data
-- statement:
--   Let $A$ be a commutative ring, $P$ a locally Noetherian scheme and $q : P \to \operatorname{Spec} A$ a morphism, and let $H, K$ be $\mathcal O$-module presheaf data on $q$: each assigns to every open $U$ of $P$ a $\Gamma(P,U)$-module (also an $A$-module, compatibly) together with $A$-linear restriction maps for $U' \le U$ that are semilinear over restriction of functions and are functorial. Assume $H$ and $K$ are each coherent, that is, $H(U)$ and $K(U)$ are finite $\Gamma(P,U)$-modules for every affine open $U$, and quasicoherent, that is, for every affine open $U$ and $f \in \Gamma(P,U)$ every section over the basic open $D(f)$ becomes a restriction after multiplication by some power of $f$, and every section over $U$ restricting to $0$ on $D(f)$ is killed by some power of $f$. Then there exist a datum $X$ on $q$ and a family $\varepsilon$ assigning to each affine open $W$, each $r \in \mathbb N$ and each surjective $\Gamma(P,W)$-linear $p : \Gamma(P,W)^r \to H(W)$ a $\Gamma(P,W)$-linear isomorphism from $X(W)$ onto $\operatorname{Hom}_{\Gamma(P,W)}(\ker p, K(W))$ modulo the image of precomposition with the inclusion $\ker p \hookrightarrow \Gamma(P,W)^r$, such that $X$ is coherent and quasicoherent and the following compatibility holds: given affine opens $W' \le W$, surjections $p$ of rank $r$ over $W$ and $p'$ of rank $r'$ over $W'$, an additive map $g : \Gamma(P,W)^r \to \Gamma(P,W')^{r'}$ semilinear over restriction with $p'(g v) = H.\mathrm{res}(p v)$, and linear maps $\delta$ on $\ker p$ and $\delta'$ on $\ker p'$ with values in $K(W)$, $K(W')$ satisfying $\delta'(g s) = K.\mathrm{res}(\delta s)$ for all $s \in \ker p$, the restriction of $\varepsilon_{W,r,p}^{-1}[\delta]$ to $W'$ equals $\varepsilon_{W',r',p'}^{-1}[\delta']$.
--
--   This constructs, in the language of $\mathcal O$-module data over a base ring, the coherent sheaf of local $\mathrm{Ext}^1$ groups: on an affine open $W$ the quotient $\operatorname{Hom}_{\Gamma(P,W)}(\ker p, K(W))/\operatorname{Hom}_{\Gamma(P,W)}(\Gamma(P,W)^r, K(W))$ attached to a finite free presentation $p$ of $H(W)$ computes $\mathrm{Ext}^1_{\Gamma(P,W)}(H(W),K(W))$, and the assertion is that these quotients glue into a coherent quasicoherent datum with the expected functoriality in presentations and in the open. It feeds the construction of chart data for proper schemes over adically complete rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_isCoherent_linearEquiv_extQuot_of_isCoherent.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_isCoherent_linearEquiv_extQuot_of_isCoherent
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsLocallyNoetherian P]
    (H K : OModulePresheaf q)
    (hHc : H.IsCoherent) (hHq : H.IsQuasicoherent) (hKc : K.IsCoherent) (hKq : K.IsQuasicoherent) :
    ∃ (X : OModulePresheaf q)
      (ε : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] H.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] K.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (K.obj W.1) (LinearMap.ker p).subtype)))),
      X.IsCoherent ∧ X.IsQuasicoherent ∧
      ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] H.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] H.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = H.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] K.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] K.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = K.res h (δ s)),
        X.res h ((ε W r p hp).symm (Submodule.Quotient.mk δ)) = (ε W' r' p' hp').symm (Submodule.Quotient.mk δ') := by sorry
