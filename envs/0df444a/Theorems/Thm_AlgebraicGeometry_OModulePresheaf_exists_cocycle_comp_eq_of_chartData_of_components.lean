-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components
-- name    : AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_components
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/d1910224-595c-5a01-a6e8-5e4d9332b03f
-- title:
--   Twisting chart data by a cocycle to make comparison maps compatible
-- statement:
--   Throughout, $A$ is a commutative ring, $P$ a scheme and $q : P \to \operatorname{Spec} A$ a morphism. An `OModulePresheaf q` consists of an assignment $U \mapsto \mathcal{G}(U)$ from the opens of $P$ to $A$-modules, each $\mathcal{G}(U)$ carrying in addition a $\Gamma(P,U)$-module structure compatible with the $A$-action through the $A$-algebra structure on $\Gamma(P,U)$ induced by $q$, together with $A$-linear restrictions $\mathcal{G}(U') \to \mathcal{G}(U)$ for $U \le U'$ that are semilinear for the restriction of sections, reflexive and transitive. A morphism `AffHom F G` is a family of $A$-linear maps $F(U) \to G(U)$ indexed by the *affine* opens $U$ of $P$, each $\Gamma(P,U)$-homogeneous, and natural for restrictions between affine opens.
--
--   The global data are: a sequence $F_k$ ($k \in \mathbb{N}$) of such presheaves with transition morphisms $\varphi_k : F_{k+1} \to F_k$; a sequence $E_k$ with morphisms $\varepsilon_k : F_k \to E_k$; a presheaf $G_E$ with morphisms $\psi^E_k : G_E \to E_k$; and a presheaf $G_K$ with morphisms $\lambda_k : G_K \to F_k$ compatible with the tower, in the sense that on every affine open $U$ one has $\varphi_k \circ \lambda_{k+1} = \lambda_k$ (hypothesis `hlamc`).
--
--   The chart data are indexed by a linearly ordered type $\iota$ together with a family of opens $U_c i$ of $P$ (no covering condition is imposed). For each $i$ and each affine open $U \le U_c i$ there is given an $A$-module $M_i(U)$, carrying also a $\Gamma(P,U)$-module structure compatible with the $A$-action, $A$-linear maps $\mathrm{res}_i : M_i(U) \to M_i(U')$ for $U' \le U$ inside $U_c i$ (no functoriality axiom is imposed on this family), and $A$-linear maps
--   $$\vartheta^i_U : G_K(U) \to M_i(U), \qquad \theta^{E,i}_U : M_i(U) \to G_E(U), \qquad \theta^{F,i}_{k,U} : M_i(U) \to F_k(U).$$
--   The hypotheses `hϑs`, `hθEs`, `hθFs` assert $\Gamma(P,U)$-homogeneity of these three families, and `hϑn`, `hθEn`, `hθFn` their naturality for the restrictions $\mathrm{res}_i$ and the restrictions of $G_K$, $G_E$, $F_k$. Further, `hexact` requires $\operatorname{im}(\vartheta^i_U) = \ker(\theta^{E,i}_U)$ for all $i, U$; `hc1` requires $\varphi_k \circ \theta^{F,i}_{k+1,U} = \theta^{F,i}_{k,U}$; `hc2` requires $\theta^{F,i}_{k,U} \circ \vartheta^i_U = \lambda_k$ at $U$; and `hc3` requires $\varepsilon_k \circ \theta^{F,i}_{k,U} = \psi^E_k \circ \theta^{E,i}_U$.
--
--   The overlap data are $A$-linear maps $u_{ij,W} : M_i(W) \to M_j(W)$, given for all $i, j$ and every affine open $W$ contained in both $U_c i$ and $U_c j$, subject to: `hub`, each $u_{ij,W}$ is bijective; `hus`, $\Gamma(P,W)$-homogeneity (for the given $\Gamma(P,W)$-structure on $M_j(W)$); `hun`, naturality for the restrictions; `huϑ`, $u_{ij,W} \circ \vartheta^i_W = \vartheta^j_W$; `huθE`, $\theta^{E,j}_W \circ u_{ij,W} = \theta^{E,i}_W$; and `hcocy`, the cocycle identity $u_{jl,W} \circ u_{ij,W} = u_{il,W}$ for all triples $i, j, l$ (with no order restriction). No compatibility of the $u_{ij}$ with the $\theta^{F,i}_k$ is assumed.
--
--   The correction data consist of three further families of $A$-linear maps. First, for $i < j$ and $W$ an affine open in $U_c i \cap U_c j$, maps $z_{ij,W} : G_E(W) \to G_K(W)$ which are $\Gamma(P,W)$-homogeneous (`hzCs`), natural for restrictions (`hzCn`), and satisfy the additive cocycle relation $z_{ij,W} + z_{jl,W} = z_{il,W}$ for $i < j < l$ on affine opens $W$ contained in $U_c i$, $U_c j$ and $U_c l$ (`hzCc`). Secondly, for each $k$, $i$ and affine open $U \le U_c i$, maps $Y_{k,i,U} : G_E(U) \to G_K(U)$, $\Gamma(P,U)$-homogeneous (`hYs`), natural (`hYn`), and satisfying $\lambda_k(Y_{k+1,i,U} v) = \lambda_k(Y_{k,i,U} v)$ for all $v$ (`hY`). Thirdly, for each $k$ and $i < j$, maps $t_{k,ij,W} : G_E(W) \to G_K(W)$, assumed merely $A$-linear, subject to two relations: `ht`, that for every $x \in M_i(W)$
--   $$\lambda_k\bigl(t_{k,ij,W}(\theta^{E,i}_W x)\bigr) = \theta^{F,j}_{k,W}(u_{ij,W} x) - \theta^{F,i}_{k,W}(x),$$
--   and `hzt`, that for every $v \in G_E(W)$
--   $$\lambda_k\bigl(z_{ij,W} v\bigr) = \lambda_k\bigl(t_{k,ij,W} v\bigr) + \lambda_k\bigl(Y_{k,j,W} v\bigr) - \lambda_k\bigl(Y_{k,i,W} v\bigr),$$
--   where on the right the maps $\lambda_k$ are taken at $W$ and $Y_{k,j}$ is the map attached to the chart $j$ at $W$.
--
--   The conclusion asserts the existence of a new family of $A$-linear comparison maps $\theta''_{i,k,U} : M_i(U) \to F_k(U)$, indexed by $i \in \iota$, $k \in \mathbb{N}$ and affine opens $U \le U_c i$, such that: (i) each $\theta''_{i,k,U}$ is $\Gamma(P,U)$-homogeneous; (ii) each is natural, i.e. $\theta''_{i,k,U'} \circ \mathrm{res}_i = (F_k).\mathrm{res} \circ \theta''_{i,k,U}$ for $U' \le U$ in $U_c i$; (iii) $\varphi_k \circ \theta''_{i,k+1,U} = \theta''_{i,k,U}$; (iv) $\theta''_{i,k,U} \circ \vartheta^i_U = \lambda_k$ at $U$; (v) $\varepsilon_k \circ \theta''_{i,k,U} = \psi^E_k \circ \theta^{E,i}_U$; and, jointly with this, the existence of a new family of $A$-linear overlap maps $u''_{ij,W} : M_i(W) \to M_j(W)$, for all $i, j$ and all affine opens $W$ contained in $U_c i$ and $U_c j$, such that: (vi) each $u''_{ij,W}$ is bijective; (vii) each is $\Gamma(P,W)$-homogeneous; (viii) each is natural for the restrictions; (ix) $u''_{ij,W} \circ \vartheta^i_W = \vartheta^j_W$; (x) $\theta^{E,j}_W \circ u''_{ij,W} = \theta^{E,i}_W$ (the original maps $\theta^E$ being unchanged); (xi) the cocycle identity $u''_{jl,W} \circ u''_{ij,W} = u''_{il,W}$ holds for all triples $i, j, l$; and (xii) the two new families are compatible: $\theta''_{j,k,W}(u''_{ij,W} x) = \theta''_{i,k,W}(x)$ for all $i, j, k, W$ and $x \in M_i(W)$.
--
--   Thus the assertion is purely existential: the corrected data are produced, and no formula expressing $\theta''$ and $u''$ in terms of $\theta^F$, $u$, $z$, $Y$ is part of the statement.
--
--   This is the component-level linear-algebra step of the twisting construction: given chart-wise extension data of $G_E$ by $G_K$ with comparison maps to a tower $(F_k, \varphi_k)$ and overlap isomorphisms, together with an additive cocycle $z$ and correction terms $Y$, $t$ measuring the failure of compatibility, it replaces the comparison maps and the overlap isomorphisms by new ones that retain all the structural properties and are in addition compatible. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle), where the correction data are obtained from a cocycle of internal homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_components.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_components
    {A : Type u} [CommRing A] {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A))
    (F : ℕ → OModulePresheaf q) (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (E : ℕ → OModulePresheaf q) (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (GE : OModulePresheaf q) (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (GK : OModulePresheaf q) (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    {ι : Type u} [LinearOrder ι] (Uc : ι → P.Opens)
    (M : ∀ i : ι, {U : P.affineOpens // U.1 ≤ Uc i} → Type u)
    [∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), AddCommGroup (M i U)]
    [∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), Module A (M i U)]
    [iΓ : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : ι) {U U' : {U : P.affineOpens // U.1 ≤ Uc i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (ϑ : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : ι) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : ι) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hc1 : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)
    (u : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : ι) (W W' : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    (hcocy : ∀ (i j l : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (hl : W.1.1 ≤ Uc l) (x : M i W),
        u j l ⟨W.1, hj⟩ hl (u i j W hj x) = u i l W hl x)

    (zC : ∀ (i j : ι), i < j → ∀ (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), GE.obj W.1.1 →ₗ[A] GK.obj W.1.1)
    (hzCs : ∀ (i j : ι) (hij : i < j) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (a : Γ(P, W.1.1)) (v : GE.obj W.1.1),
      zC i j hij W hj (a • v) = a • zC i j hij W hj v)
    (hzCn : ∀ (i j : ι) (hij : i < j) (W W' : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (h : W'.1.1 ≤ W.1.1) (v : GE.obj W.1.1),
      zC i j hij W' (h.trans hj) (GE.res h v) = GK.res h (zC i j hij W hj v))
    (hzCc : ∀ (i j l : ι) (hij : i < j) (hjl : j < l) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (hl : W.1.1 ≤ Uc l) (v : GE.obj W.1.1),
      zC i j hij W hj v + zC j l hjl ⟨W.1, hj⟩ hl v = zC i l (hij.trans hjl) W hl v)

    (YC : ∀ (k : ℕ) (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}), GE.obj U.1.1 →ₗ[A] GK.obj U.1.1)
    (hYs : ∀ (k : ℕ) (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (v : GE.obj U.1.1), YC k i U (a • v) = a • YC k i U v)
    (hYn : ∀ (k : ℕ) (i : ι) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (v : GE.obj U.1.1),
      YC k i U' (GE.res h v) = GK.res h (YC k i U v))
    (hY : ∀ (k : ℕ) (i : ι) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (v : GE.obj U.1.1), (lam k).app U.1 (YC (k + 1) i U v) = (lam k).app U.1 (YC k i U v))

    (tC : ∀ (k : ℕ) (i j : ι), i < j → ∀ (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), GE.obj W.1.1 →ₗ[A] GK.obj W.1.1)
    (ht : ∀ (k : ℕ) (i j : ι) (hij : i < j) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : M i W),
      (lam k).app W.1 (tC k i j hij W hj (θE i W x)) = θF j k ⟨W.1, hj⟩ (u i j W hj x) - θF i k W x)
    (hzt : ∀ (k : ℕ) (i j : ι) (hij : i < j) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (v : GE.obj W.1.1),
      (lam k).app W.1 (zC i j hij W hj v) =
        (lam k).app W.1 (tC k i j hij W hj v) + (lam k).app W.1 (YC k j ⟨W.1, hj⟩ v) - (lam k).app W.1 (YC k i W v))
    :
    ∃ (θF'' : ∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), M i U →ₗ[A] (F k).obj U.1.1),
      (∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF'' i k U (a • x) = a • θF'' i k U x) ∧
      (∀ (i : ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ Uc i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF'' i k U' (res i h x) = (F k).res h (θF'' i k U x)) ∧
      (∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), (φ k).app U.1 ∘ₗ θF'' i (k + 1) U = θF'' i k U) ∧
      (∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), θF'' i k U ∘ₗ ϑ i U = (lam k).app U.1) ∧
      (∀ (i : ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ Uc i}), (ε k).app U.1 ∘ₗ θF'' i k U = (ψE k).app U.1 ∘ₗ θE i U) ∧
    ∃ (u'' : ∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), M i W →ₗ[A] M j ⟨W.1, hj⟩),
      (∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j), Function.Bijective (u'' i j W hj)) ∧
      (∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u'' i j W hj (a • x) = a • u'' i j W hj x) ∧
      (∀ (i j : ι) (W W' : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u'' i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u'' i j W hj x)) ∧
      (∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : GK.obj W.1.1), u'' i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x) ∧
      (∀ (i j : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : M i W), θE j ⟨W.1, hj⟩ (u'' i j W hj x) = θE i W x) ∧

      (∀ (i j l : ι) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (hl : W.1.1 ≤ Uc l) (x : M i W),
        u'' j l ⟨W.1, hj⟩ hl (u'' i j W hj x) = u'' i l W hl x) ∧
      (∀ (i j : ι) (k : ℕ) (W : {U : P.affineOpens // U.1 ≤ Uc i}) (hj : W.1.1 ≤ Uc j) (x : M i W),
        θF'' j k ⟨W.1, hj⟩ (u'' i j W hj x) = θF'' i k W x) := by sorry
