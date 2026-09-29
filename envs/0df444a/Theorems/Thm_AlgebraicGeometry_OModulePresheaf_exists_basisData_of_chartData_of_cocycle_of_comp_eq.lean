-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq
-- name    : AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_cocycle_of_comp_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/ac6d4398-af0f-59eb-8ce0-bf86d09136d3
-- title:
--   Gluing chart-wise extension data along a cocycle
-- statement:
--   The ambient frame consists of a Noetherian commutative ring $A$ of universe level $u$, an ideal $I \subseteq A$ for which $A$ is $I$-adically complete, a scheme $P$, and a proper morphism $q : P \to \operatorname{Spec} A$. Throughout, $\Gamma(P,U)$ denotes the sections of the structure sheaf on an open $U$, regarded as an $A$-algebra via $q$ (`Scheme.TwoAffineOpenCover.algebraOfHom`), and an `OModulePresheaf q` is the project's notion of a presheaf of modules: an assignment $U \mapsto F.\mathrm{obj}\,U$ of $u$-small abelian groups to the opens of $P$, each carrying an $A$-module and a $\Gamma(P,U)$-module structure forming a scalar tower over $A$, together with $A$-linear restrictions $F.\mathrm{res} : U \le U' \to F.\mathrm{obj}\,U' \to F.\mathrm{obj}\,U$ that are semilinear for the $\Gamma$-actions and satisfy reflexivity and transitivity. An `AffHom F G` is a family of $A$-linear maps $F.\mathrm{obj}\,U \to G.\mathrm{obj}\,U$ indexed by the affine opens $U$ of $P$, semilinear for the $\Gamma(P,U)$-actions and natural for restrictions between affine opens; `IsCoherent F` says that $F.\mathrm{obj}\,U$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and `IsQuasicoherent F` says that for every affine open $U$ and every $g \in \Gamma(P,U)$ each section over the basic open $P.\mathrm{basicOpen}\,g$ becomes, after multiplication by some power of $g$, the restriction of a section over $U$, and every section over $U$ restricting to $0$ on $P.\mathrm{basicOpen}\,g$ is killed by some power of $g$.
--
--   The first block of data is two towers of presheaves of modules. There are $F : \mathbb{N} \to$ `OModulePresheaf q`, coherent (`hFc`) and quasi-coherent (`hFq`), with affine morphisms $\varphi_k : F(k+1) \to F(k)$ whose components on each affine open $U$ are surjective (`hφs`) with kernel $I^{k+1} \cdot \top$ inside $F(k+1).\mathrm{obj}\,U$ (`hφk`); and likewise $E : \mathbb{N} \to$ `OModulePresheaf q`, coherent (`hEc`) and quasi-coherent (`hEq`), with $\tau_k : E(k+1) \to E(k)$ surjective on affine opens (`hτs`) with kernel $I^{k+1} \cdot \top$ (`hτk`). Morphisms $\varepsilon_k : F(k) \to E(k)$ are surjective on each affine open (`hεs`) and satisfy $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$ on each affine open (`hεc`). Further, $GE$ is a coherent (`hGEc`) quasi-coherent (`hGEq`) presheaf of modules with morphisms $\psi E_k : GE \to E(k)$ that are surjective on affine opens (`hψEs`), have kernel $I^{k+1} \cdot \top$ in $GE.\mathrm{obj}\,U$ (`hψEk`) and satisfy $\tau_k \circ \psi E_{k+1} = \psi E_k$ (`hψEc`); and $GK$ is a coherent (`hGKc`) quasi-coherent (`hGKq`) presheaf of modules with morphisms $\lambda_k : GK \to F(k)$ satisfying $\varphi_k \circ \lambda_{k+1} = \lambda_k$ (`hlamc`), $\operatorname{range}(\lambda_k|_U) = \ker(\varepsilon_k|_U)$ for every affine open $U$ (`hlamr`), and the shift condition `hlami`: for every affine open $U$ there is $c \in \mathbb{N}$ with $\ker(\lambda_{k+c}|_U) \le I^{k+1} \cdot \top$ in $GK.\mathrm{obj}\,U$ for all $k$.
--
--   The second block is chart data relative to an ordered affine cover $K$ of $P$ (a finite linearly ordered index type $K.\iota$ together with opens $K.U\,i$, each affine, whose supremum is $\top$). For each $i \in K.\iota$ and each affine open $U$ of $P$ with $U \le K.U\,i$, there is a $u$-small module $M\,i\,U$ carrying compatible $A$- and $\Gamma(P,U)$-module structures forming a scalar tower over $A$, together with $A$-linear restriction maps $\mathrm{res}\,i\,h : M\,i\,U \to M\,i\,U'$ for $U' \le U$ inside $K.U\,i$. These are subject to: semilinearity for the $\Gamma$-actions (`res_smul`), $\mathrm{res}$ along the identity being the identity (`res_refl`), and transitivity (`res_comp`); the quasi-coherence hypothesis `hqc`, which for $U_g = P.\mathrm{basicOpen}\,g$ with $g \in \Gamma(P,U)$ asserts the two usual clauses (every element of $M\,i\,U_g$ becomes $g^n$ times the restriction of an element of $M\,i\,U$ for some $n$, and every element of $M\,i\,U$ restricting to $0$ is annihilated by a power of $g$); and finiteness of $M\,i\,U$ over $\Gamma(P,U)$ (`hfg`). Comparison maps are given: $\vartheta\,i\,U : GK.\mathrm{obj}\,U \to M\,i\,U$, $\theta E\,i\,U : M\,i\,U \to GE.\mathrm{obj}\,U$ and $\theta F\,i\,k\,U : M\,i\,U \to F(k).\mathrm{obj}\,U$, all $A$-linear, all semilinear for the $\Gamma(P,U)$-actions (`hϑs`, `hθEs`, `hθFs`) and all commuting with restrictions (`hϑn`, `hθEn`, `hθFn`). They satisfy exactness $\operatorname{range}(\vartheta\,i\,U) = \ker(\theta E\,i\,U)$ (`hexact`), surjectivity of $\theta E\,i\,U$ (`hsurj`), injectivity of $\vartheta\,i\,U$ (`hϑi`), and the three compatibilities $\varphi_k \circ \theta F\,i\,(k+1)\,U = \theta F\,i\,k\,U$ (`hc1`), $\theta F\,i\,k\,U \circ \vartheta\,i\,U = \lambda_k|_U$ (`hc2`) and $\varepsilon_k|_U \circ \theta F\,i\,k\,U = \psi E_k|_U \circ \theta E\,i\,U$ (`hc3`).
--
--   The third block is the overlap data: for indices $i, j$ and an affine open $W \le K.U\,i$ with also $W \le K.U\,j$, an $A$-linear map $u\,i\,j\,W : M\,i\,W \to M\,j\,W$ (the target taken with $W$ viewed as an affine open below $K.U\,j$), which is bijective (`hub`), semilinear for the $\Gamma(P,W)$-action (`hus`), commutes with restrictions to smaller affine opens contained in both charts (`hun`), satisfies $u\,i\,j\,W \circ \vartheta\,i\,W = \vartheta\,j\,W$ (`huϑ`), $\theta E\,j\,W \circ u\,i\,j\,W = \theta E\,i\,W$ (`huθE`), the cocycle identity $u\,j\,l\,W \circ u\,i\,j\,W = u\,i\,l\,W$ on any triple of charts containing $W$ (`hcocy`), and $\theta F\,j\,k\,W \circ u\,i\,j\,W = \theta F\,i\,k\,W$ for every $k$ (`huθF`).
--
--   The conclusion asserts the existence of a set $B$ of affine opens of $P$ which is downward closed ($W' \le W$ and $W \in B$ imply $W' \in B$) and covers $P$ (every point of $P$ lies in some member of $B$), together with: a $u$-small module $M\,W$ for each $W \in B$, carrying an abelian group structure, an $A$-module structure, a $\Gamma(P,W)$-module structure and the scalar tower over $A$; $A$-linear restrictions $\mathrm{res}\,h : M\,W \to M\,W'$ for $W' \le W$ in $B$, semilinear for the $\Gamma$-actions, equal to the identity along the identity inclusion and transitive; the two quasi-coherence clauses for basic opens $W_g = P.\mathrm{basicOpen}\,g$ with $W, W_g \in B$ and $g \in \Gamma(P,W)$ (divisibility by a power of $g$ of sections over $W_g$, and annihilation by a power of $g$ of sections over $W$ restricting to $0$); finiteness of each $M\,W$ over $\Gamma(P,W)$; and $A$-linear maps $\vartheta\,W : GK.\mathrm{obj}\,W \to M\,W$, $\theta E\,W : M\,W \to GE.\mathrm{obj}\,W$ and $\theta F\,k\,W : M\,W \to F(k).\mathrm{obj}\,W$, such that the following eleven statements hold: $\vartheta\,W$, $\theta E\,W$ and each $\theta F\,k\,W$ are semilinear for the $\Gamma(P,W)$-actions; $\vartheta$ commutes with the restrictions of $GK$, $\theta E$ with those of $GE$, and each $\theta F\,k$ with those of $F(k)$, in each case along the restrictions of the family $M$; $\operatorname{range}(\vartheta\,W) = \ker(\theta E\,W)$ for every $W \in B$; $\theta E\,W$ is surjective for every $W \in B$; and, for all $k$ and all $W \in B$, $\varphi_k|_W \circ \theta F\,(k+1)\,W = \theta F\,k\,W$, $\theta F\,k\,W \circ \vartheta\,W = \lambda_k|_W$ and $\varepsilon_k|_W \circ \theta F\,k\,W = \psi E_k|_W \circ \theta E\,W$. Note that, unlike the chart data, the glued data is not required to have $\vartheta\,W$ injective.
--
--   This is the gluing step of a descent argument: chart-wise families of modules over the members of an ordered affine cover, equipped with comparison maps to the towers $F$, $E$ and to $GK$, $GE$, are assembled into a single family indexed by the downward-closed basis of affine opens contained in some chart, the overlap isomorphisms $u$ and their cocycle condition providing the restrictions and the transport of all comparison maps. It feeds the extension statement [`AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_isProper_of_isAdicComplete), used in the construction of coherent sheaves over the $I$-adically complete base from their reductions.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_basisData_of_chartData_of_cocycle_of_comp_eq.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_cocycle_of_comp_eq
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
    (hcocy : ∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u j l ⟨W.1, hj⟩ hl (u i j W hj x) = u i l W hl x)
    (huθF : ∀ (i j : K.ι) (k : ℕ) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θF j k ⟨W.1, hj⟩ (u i j W hj x) = θF i k W x)
    :
    ∃ (B : Set P.affineOpens)
      (_hdown : ∀ (W W' : P.affineOpens), W'.1 ≤ W.1 → W ∈ B → W' ∈ B)
      (_hcov : ∀ x : P, ∃ W ∈ B, x ∈ W.1)
      (M : ↥B → Type u) (_ : ∀ W, AddCommGroup (M W)) (_ : ∀ W, Module A (M W)) (_ : ∀ W, Module Γ(P, W.1.1) (M W))
      (_ : ∀ W : ↥B, letI := Scheme.TwoAffineOpenCover.algebraOfHom q W.1.1; IsScalarTower A Γ(P, W.1.1) (M W))
      (res : ∀ {W W' : ↥B}, W'.1.1 ≤ W.1.1 → (M W →ₗ[A] M W'))
      (_res_smul : ∀ {W W' : ↥B} (h : W'.1.1 ≤ W.1.1) (a : Γ(P, W.1.1)) (x : M W),
        res h (a • x) = (P.presheaf.map (homOfLE h).op).hom a • res h x)
      (_res_refl : ∀ (W : ↥B) (x : M W), res (le_refl W.1.1) x = x)
      (_res_comp : ∀ {W W' W'' : ↥B} (h : W''.1.1 ≤ W'.1.1) (h' : W'.1.1 ≤ W.1.1) (x : M W),
        res (h.trans h') x = res h (res h' x))
      (_hqc : ∀ (W Wg : ↥B) (g : Γ(P, W.1.1)) (hWg : Wg.1.1 = P.basicOpen g),
        (∀ y : M Wg, ∃ (n : ℕ) (x : M W),
            res (hWg.trans_le (P.basicOpen_le g)) x =
              (P.presheaf.map (homOfLE (hWg.trans_le (P.basicOpen_le g))).op).hom (g ^ n) • y) ∧
        (∀ x : M W, res (hWg.trans_le (P.basicOpen_le g)) x = 0 → ∃ n : ℕ, (g ^ n) • x = 0))
      (_hfg : ∀ W : ↥B, Module.Finite (Γ(P, W.1.1) : Type u) (M W))

      (ϑ : ∀ W : ↥B, GK.obj W.1.1 →ₗ[A] M W)
      (θE : ∀ W : ↥B, M W →ₗ[A] GE.obj W.1.1)
      (θF : ∀ (k : ℕ) (W : ↥B), M W →ₗ[A] (F k).obj W.1.1),

      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : GK.obj W.1.1), ϑ W (a • x) = a • ϑ W x) ∧
      (∀ (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θE W (a • x) = a • θE W x) ∧
      (∀ (k : ℕ) (W : ↥B) (a : Γ(P, W.1.1)) (x : M W), θF k W (a • x) = a • θF k W x) ∧

      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : GK.obj W.1.1), ϑ W' (GK.res h x) = res h (ϑ W x)) ∧
      (∀ (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θE W' (res h x) = GE.res h (θE W x)) ∧
      (∀ (k : ℕ) (W W' : ↥B) (h : W'.1.1 ≤ W.1.1) (x : M W), θF k W' (res h x) = (F k).res h (θF k W x)) ∧

      (∀ W : ↥B, LinearMap.range (ϑ W) = LinearMap.ker (θE W)) ∧
      (∀ W : ↥B, Function.Surjective (θE W)) ∧

      (∀ (k : ℕ) (W : ↥B), (φ k).app W.1 ∘ₗ θF (k + 1) W = θF k W) ∧
      (∀ (k : ℕ) (W : ↥B), θF k W ∘ₗ ϑ W = (lam k).app W.1) ∧
      (∀ (k : ℕ) (W : ↥B), (ε k).app W.1 ∘ₗ θF k W = (ψE k).app W.1 ∘ₗ θE W) := by sorry
