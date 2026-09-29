-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/336a7dfa-a448-5ca0-b208-2a948e4a6bf1
-- title:
--   Correcting overlap isomorphisms of chart extensions to a cocycle
-- statement:
--   Fix a Noetherian commutative ring $A$, an ideal $I \subseteq A$ with $A$ $I$-adically complete, a scheme $P$ and a proper morphism $q : P \to \operatorname{Spec} A$.
--
--   Throughout, an object of `OModulePresheaf q` is a presheaf-like datum assigning to every open $U$ of $P$ an abelian group with compatible $A$-module and $\Gamma(P,U)$-module structures (the $A$-action factoring through $\Gamma(P,U)$ via the algebra structure coming from $q$), together with $A$-linear restriction maps $\mathrm{res}_h$ for $U \le U'$ that are semilinear over the restriction of sections and satisfy the reflexivity and transitivity identities. Such a datum is `IsCoherent` when each $F(U)$, for $U$ affine open, is a finite $\Gamma(P,U)$-module, and `IsQuasicoherent` when for every affine open $U$ and every $g \in \Gamma(P,U)$ each section over $P.basicOpen\,g$ becomes, after multiplication by some power of $g$, the restriction of a section over $U$, and every section over $U$ restricting to zero over $P.basicOpen\,g$ is annihilated by some power of $g$. An `AffHom F G` is a family of $\Gamma(P,U)$-linear maps $F(U) \to G(U)$ indexed by the affine opens $U$, commuting with the restriction maps.
--
--   *Two towers.* Families $F_k$ and $E_k$ ($k \in \mathbb{N}$) of such data are given, all coherent and quasicoherent (`hFc`, `hFq`, `hEc`, `hEq`), together with `AffHom`s $\varphi_k : F_{k+1} \to F_k$ and $\tau_k : E_{k+1} \to E_k$ which on every affine open $U$ are surjective (`hφs`, `hτs`) with kernel exactly $I^{k+1} \cdot F_{k+1}(U)$, resp. $I^{k+1} \cdot E_{k+1}(U)$ (`hφk`, `hτk`); and `AffHom`s $\varepsilon_k : F_k \to E_k$, surjective on every affine open (`hεs`) and satisfying $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$ on every affine open (`hεc`).
--
--   *The two limit data.* A coherent quasicoherent $G_E$ (`hGEc`, `hGEq`) is given with `AffHom`s $\psi_{E,k} : G_E \to E_k$ which on each affine open are surjective (`hψEs`) with kernel $I^{k+1} \cdot G_E(U)$ (`hψEk`) and satisfy $\tau_k \circ \psi_{E,k+1} = \psi_{E,k}$ (`hψEc`); and a coherent quasicoherent $G_K$ (`hGKc`, `hGKq`) with `AffHom`s $\lambda_k : G_K \to F_k$ satisfying $\varphi_k \circ \lambda_{k+1} = \lambda_k$ (`hlamc`), $\operatorname{range} \lambda_k(U) = \ker \varepsilon_k(U)$ on every affine open $U$ (`hlamr`), and the shifted kernel bound `hlami`: for every affine open $U$ there is $c \in \mathbb{N}$ with $\ker \lambda_{k+c}(U) \subseteq I^{k+1} \cdot G_K(U)$ for all $k$.
--
--   *The cover.* $K$ is an `OrderedAffineCover` of $P$: a finite linearly ordered index type $K.\iota$ together with opens $K.U\,i$, each affine, whose supremum is $\top$.
--
--   *The chart modules.* For each $i \in K.\iota$ and each affine open $U$ of $P$ contained in $K.U\,i$ (the index set being the subtype of such $U$) a type $M_i(U)$ is given, carrying an abelian group structure, an $A$-module structure, a $\Gamma(P,U)$-module structure `iΓ` and the corresponding scalar tower; together with $A$-linear restriction maps $\mathrm{res}_i$ along inclusions of charts in $K.U\,i$, semilinear over restriction of sections (`res_smul`), reflexive (`res_refl`) and transitive (`res_comp`). The hypothesis `hqc` requires of each $M_i$ the quasicoherence condition relative to basic opens: for charts $U$, $U_g$ in $K.U\,i$ and $g \in \Gamma(P,U)$ with $U_g = P.basicOpen\,g$, every $y \in M_i(U_g)$ satisfies $\mathrm{res}_i(x) = (g^n|_{U_g}) \cdot y$ for some $n$ and some $x \in M_i(U)$, and every $x \in M_i(U)$ with $\mathrm{res}_i(x) = 0$ is annihilated by some $g^n$. The hypothesis `hfg` requires each $M_i(U)$ to be finite over $\Gamma(P,U)$.
--
--   *The comparison maps.* $A$-linear maps $\vartheta_{i,U} : G_K(U) \to M_i(U)$, $\theta^E_{i,U} : M_i(U) \to G_E(U)$ and $\theta^F_{i,k,U} : M_i(U) \to F_k(U)$ are given, all $\Gamma(P,U)$-linear (`hϑs`, `hθEs`, `hθFs`) and compatible with restrictions in the chart (`hϑn`, `hθEn`, `hθFn`). They are subject to: exactness $\operatorname{range} \vartheta_{i,U} = \ker \theta^E_{i,U}$ (`hexact`), surjectivity of $\theta^E_{i,U}$ (`hsurj`), injectivity of $\vartheta_{i,U}$ (`hϑi`), and the three compatibilities $\varphi_k \circ \theta^F_{i,k+1,U} = \theta^F_{i,k,U}$ (`hc1`), $\theta^F_{i,k,U} \circ \vartheta_{i,U} = \lambda_k(U)$ (`hc2`), and $\varepsilon_k \circ \theta^F_{i,k,U} = \psi_{E,k} \circ \theta^E_{i,U}$ (`hc3`).
--
--   *The overlap maps.* Finally a family $u$ is given: for all $i, j \in K.\iota$, every chart $W$ in $K.U\,i$ and every proof that $W \le K.U\,j$, an $A$-linear map $u_{i j, W} : M_i(W) \to M_j(W)$ (the target being $M_j$ at $W$ viewed as a chart in $K.U\,j$), which is bijective (`hub`), $\Gamma(P,W)$-linear for the module structure `iΓ` on the target (`hus`), compatible with the chart restrictions (`hun`), and satisfies $u_{i j, W} \circ \vartheta_{i,W} = \vartheta_{j,W}$ (`huϑ`) and $\theta^E_{j,W} \circ u_{i j, W} = \theta^E_{i,W}$ (`huθE`).
--
--   *Conclusion.* There exists a family $u'$ of the same shape — for all $i, j$, every chart $W$ in $K.U\,i$ with $W \le K.U\,j$, an $A$-linear map $M_i(W) \to M_j(W)$ — such that:
--
--   1. every $u'_{i j, W}$ is bijective;
--
--   2. every $u'_{i j, W}$ is $\Gamma(P,W)$-linear, for the module structure `iΓ` on the target;
--
--   3. $u'$ commutes with the chart restrictions: $u'_{i j, W'}(\mathrm{res}_i\, x) = \mathrm{res}_j\, (u'_{i j, W}\, x)$ for $W' \le W$;
--
--   4. $u'_{i j, W}(\vartheta_{i,W}\, x) = \vartheta_{j,W}\, x$ for all $x \in G_K(W)$;
--
--   5. $\theta^E_{j,W}(u'_{i j, W}\, x) = \theta^E_{i,W}\, x$ for all $x \in M_i(W)$;
--
--   6. the cocycle identity holds: for all $i, j, l \in K.\iota$, every chart $W$ in $K.U\,i$ with $W \le K.U\,j$ and $W \le K.U\,l$, and every $x \in M_i(W)$,
--   $$u'_{j l, W}\bigl(u'_{i j, W}\, x\bigr) = u'_{i l, W}\, x .$$
--
--   No relation between $u'$ and the given family $u$ is asserted, and no compatibility of $u'$ with the maps $\theta^F_{i,k}$ is asserted.
--
--   This is the cocycle-correction step in the descent of chart-wise extension data on a proper scheme over a complete Noetherian base: the discrepancy $u_{jl}u_{ij} - u_{il}$ is measured by a Čech $2$-cochain with values in an internal Hom datum, and the statement records that the overlap isomorphisms can be modified so that the discrepancy vanishes identically. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_isProper_of_isAdicComplete), where the corrected family is glued to a global object.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_of_chartData_of_isProper_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) [IsAdicComplete I A]
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q) (hEc : ∀ k, (E k).IsCoherent) (hEq : ∀ k, (E k).IsQuasicoherent)
    (τ : ∀ k, OModulePresheaf.AffHom (E (k + 1)) (E k))
    (hτs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((τ k).app U))
    (hτk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((τ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((E (k + 1)).obj U.1)))
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (hεs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ε k).app U))
    (hεc : ∀ (k : ℕ) (U : P.affineOpens),
      (τ k).app U ∘ₗ (ε (k + 1)).app U = (ε k).app U ∘ₗ (φ k).app U)
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
    (hψEs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((ψE k).app U))
    (hψEk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((ψE k).app U) = I ^ (k + 1) • (⊤ : Submodule A (GE.obj U.1)))
    (hψEc : ∀ (k : ℕ) (U : P.affineOpens), (τ k).app U ∘ₗ (ψE (k + 1)).app U = (ψE k).app U)
    (GK : OModulePresheaf q) (hGKc : GK.IsCoherent) (hGKq : GK.IsQuasicoherent)
    (lam : ∀ k, OModulePresheaf.AffHom GK (F k))
    (hlamc : ∀ (k : ℕ) (U : P.affineOpens), (φ k).app U ∘ₗ (lam (k + 1)).app U = (lam k).app U)
    (hlamr : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.range ((lam k).app U) = LinearMap.ker ((ε k).app U))
    (hlami : ∀ U : P.affineOpens, ∃ c : ℕ, ∀ k : ℕ,
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1)))
    (K : P.OrderedAffineCover)
    (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U)]
    [iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U)]
    [∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
        letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U)]
    (res : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}}, U'.1.1 ≤ U.1.1 → (M i U →ₗ[A] M i U'))
    (res_smul : ∀ (i : K.ι) {U U' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U'.1.1 ≤ U.1.1) (a : Γ(P, U.1.1)) (x : M i U),
        res i h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res i h x)
    (res_refl : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (x : M i U), res i (le_refl U.1.1) x = x)
    (res_comp : ∀ (i : K.ι) {U U' U'' : {U : P.affineOpens // U.1 ≤ K.U i}} (h : U''.1.1 ≤ U'.1.1) (h' : U'.1.1 ≤ U.1.1)
        (x : M i U), res i (h.trans h') x = res i h (res i h' x))
    (hqc : ∀ (i : K.ι) (U Ug : {U : P.affineOpens // U.1 ≤ K.U i}) (g : Γ(P, U.1.1)) (hUg : Ug.1.1 = P.basicOpen g),
        (∀ y : M i Ug, ∃ (n : ℕ) (x : M i U),
            res i (hUg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hUg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M i U, res i (hUg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
    (hfg : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module.Finite (Γ(P, U.1.1) : Type u) (M i U))
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hϑn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : GK.obj U.1.1),
        ϑ i U' (GK.res h x) = res i h (ϑ i U x))
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hϑi : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Injective (ϑ i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
    (hub : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u i j W hj))
    (hus : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u i j W hj (a • x) = a • u i j W hj x)
    (hun : ∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u i j W hj x))
    (huϑ : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1),
        u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x)
    (huθE : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x)
    :
    ∃ (u' : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u' i j W hj)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u' i j W hj (a • x) = a • u' i j W hj x) ∧
      (∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u' i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u' i j W hj x)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1), u' i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W), θE j ⟨W.1, hj⟩ (u' i j W hj x) = θE i W x) ∧

      (∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u' j l ⟨W.1, hj⟩ hl (u' i j W hj x) = u' i l W hl x) := by sorry
