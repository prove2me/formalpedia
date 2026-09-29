-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData
-- name    : AlgebraicGeometry.OModulePresheaf.exists_cochain_internalHom_forall_eq_comp_sub_of_chartData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/227a79a0-b820-5596-b60a-ab1ebe14fa91
-- title:
--   Čech 2-cochain of the overlap defect of chart-wise extensions
-- statement:
--   Throughout, $A$ is a commutative Noetherian ring, $I \subseteq A$ an ideal with $A$ $I$-adically complete, and $q : P \to \operatorname{Spec} A$ a proper morphism of schemes. Recall the project's notion of an `OModulePresheaf q`: a rule assigning to each open $U \subseteq P$ an $A$-module $F(U)$ carrying also a $\Gamma(P,U)$-module structure compatible with the $A$-algebra structure on $\Gamma(P,U)$ induced by $q$, together with $A$-linear restriction maps $F.res : F(U') \to F(U)$ for $U \le U'$ which are semilinear for presheaf restriction of scalars and satisfy the identity and composition laws. An `AffHom F G` consists of $A$-linear maps $F(U) \to G(U)$ for every affine open $U$, each $\Gamma(P,U)$-linear, commuting with restrictions. For such an $F$, `IsCoherent` asserts that $F(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and `IsQuasicoherent` asserts, for every affine open $U$ and $f \in \Gamma(P,U)$, that every section over $P.basicOpen\,f$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and that a section over $U$ restricting to $0$ on $P.basicOpen\,f$ is annihilated by a power of $f$.
--
--   Two towers are given. The first consists of $F_k$ ($k \in \mathbb{N}$), coherent (`hFc`) and quasicoherent (`hFq`), with transition maps $\varphi_k : F_{k+1} \to F_k$ in `AffHom`, surjective on every affine open (`hφs`) and with $\ker \varphi_k(U) = I^{k+1} \cdot F_{k+1}(U)$ (`hφk`). The second consists of $E_k$, coherent (`hEc`) and quasicoherent (`hEq`), with $\tau_k : E_{k+1} \to E_k$ surjective on affine opens (`hτs`) and with $\ker \tau_k(U) = I^{k+1} \cdot E_{k+1}(U)$ (`hτk`). They are linked by $\varepsilon_k : F_k \to E_k$, surjective on affine opens (`hεs`) and making the squares commute, $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$ on each affine open (`hεc`).
--
--   Two limit objects are given. First $G_E$, coherent (`hGEc`) and quasicoherent (`hGEq`), with maps $\psi^E_k : G_E \to E_k$ that are surjective on affine opens (`hψEs`), have $\ker \psi^E_k(U) = I^{k+1} \cdot G_E(U)$ (`hψEk`), and are compatible, $\tau_k \circ \psi^E_{k+1} = \psi^E_k$ (`hψEc`). Second $G_K$, coherent (`hGKc`) and quasicoherent (`hGKq`), with maps $\lambda_k : G_K \to F_k$ compatible with the tower, $\varphi_k \circ \lambda_{k+1} = \lambda_k$ (`hlamc`), with $\operatorname{range} \lambda_k(U) = \ker \varepsilon_k(U)$ on every affine open (`hlamr`), and satisfying the shift condition `hlami`: for every affine open $U$ there is $c \in \mathbb{N}$ with $\ker \lambda_{k+c}(U) \le I^{k+1} \cdot G_K(U)$ for all $k$.
--
--   Next, $K$ is an `OrderedAffineCover` of $P$: a finite linearly ordered index type $K.\iota$ together with opens $K.U\,i$, each affine, whose supremum is $\top$.
--
--   The chart data consist of: for each $i \in K.\iota$ and each affine open $W$ of $P$ with $W \le K.U\,i$, a type $M_i(W)$ which is an additive group, an $A$-module and a $\Gamma(P,W)$-module with $A$–$\Gamma(P,W)$ scalar tower (routine typeclass assumptions); $A$-linear restriction maps $res_i$ for $W' \le W$ below the chart $K.U\,i$, semilinear for presheaf restriction (`res_smul`) and satisfying the identity (`res_refl`) and composition (`res_comp`) laws; the hypothesis `hqc`, which imposes on each $M_i$ the two quasicoherence clauses above for basic opens $U_g = P.basicOpen\,g$ sitting below the chart; and `hfg`, finiteness of $M_i(W)$ over $\Gamma(P,W)$.
--
--   The comparison maps with the global data are: $\vartheta_i(W) : G_K(W) \to M_i(W)$, $\theta^E_i(W) : M_i(W) \to G_E(W)$ and $\theta^F_{i,k}(W) : M_i(W) \to F_k(W)$, all $A$-linear; they are $\Gamma(P,W)$-linear (`hϑs`, `hθEs`, `hθFs`) and natural with respect to restriction below the chart (`hϑn`, `hθEn`, `hθFn`). Exactness and extension conditions: $\operatorname{range} \vartheta_i(W) = \ker \theta^E_i(W)$ (`hexact`), $\theta^E_i(W)$ surjective (`hsurj`), $\vartheta_i(W)$ injective (`hϑi`). Compatibilities: $\varphi_k \circ \theta^F_{i,k+1} = \theta^F_{i,k}$ (`hc1`), $\theta^F_{i,k} \circ \vartheta_i = \lambda_k$ (`hc2`), and $\varepsilon_k \circ \theta^F_{i,k} = \psi^E_k \circ \theta^E_i$ (`hc3`), all on affine opens below the chart.
--
--   Finally, the overlap data: for $i, j \in K.\iota$ and an affine open $W \le K.U\,i$ with also $W \le K.U\,j$, an $A$-linear map $u_{ij}(W) : M_i(W) \to M_j(W)$, which is bijective (`hub`), $\Gamma(P,W)$-linear for the two $\Gamma(P,W)$-structures (`hus`), natural with respect to restriction to smaller affine opens (`hun`), and compatible with the extension maps: $u_{ij} \circ \vartheta_i = \vartheta_j$ (`huϑ`) and $\theta^E_j \circ u_{ij} = \theta^E_i$ (`huθE`).
--
--   Under these hypotheses there exists a Čech $2$-cochain $g$ of the internal-Hom datum $\mathcal{H}om(G_E, G_K) =$ `internalHom GE GK` for the cover $K$; that is, for each strictly increasing $s : \mathrm{Fin}\,3 \to K.\iota$ (an element of `K.Idx 2`) a section of `internalHom GE GK` over $K.inter\,s = \bigsqcap_j K.U(s_j)$, which by definition is a family assigning to each affine open $W \le K.inter\,s$ an $A$-linear map $(g\,s).1\,W : G_E(W) \to G_K(W)$, these maps being $\Gamma(P,W)$-linear and compatible with restriction between affine opens below $K.inter\,s$, such that for every such $s$, every affine open $W \le K.inter\,s$ and every $x \in M_{s_0}(W)$ (where $W$ is regarded as lying below each of $K.U(s_0)$, $K.U(s_1)$, $K.U(s_2)$ via $K.inter\_le$),
--   $$\vartheta_{s_2}\bigl((g\,s).1\,W\,(\theta^E_{s_0}(x))\bigr) = u_{s_1 s_2}\bigl(u_{s_0 s_1}(x)\bigr) - u_{s_0 s_2}(x).$$
--
--   This is the construction of the Čech $2$-cochain measuring the failure of the chart-wise comparison isomorphisms $u_{ij}$ between the extensions $0 \to G_K \to M_i \to G_E \to 0$ to compose strictly on triple overlaps; since both $u_{s_1 s_2} u_{s_0 s_1}$ and $u_{s_0 s_2}$ are morphisms of extensions inducing the identity on $G_K$ and on $G_E$, their difference factors through $\vartheta$ and $\theta^E$ by a section of $\mathcal{H}om(G_E, G_K)$, and the proof cites [`LinearMap.existsUnique_sub_eq_comp_comp_of_extension`](thm.html#LinearMap.existsUnique_sub_eq_comp_comp_of_extension) for this factorisation. It feeds the subsequent cocycle statement [`AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete), within the formal-to-algebraic existence machinery used for deformation-theoretic constructions over complete Noetherian base rings.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_cochain_internalHom_forall_eq_comp_sub_of_chartData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_cochain_internalHom_forall_eq_comp_sub_of_chartData
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
    ∃ g : (OModulePresheaf.internalHom GE GK).cochain K 2,
      ∀ (s : K.Idx 2) (W : {U : P.affineOpens // U.1 ≤ K.inter s})
        (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩),
        ϑ (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩ ((g s).1 W (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
          u (s.1 1) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (W.2.trans (K.inter_le s 2))
              (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) -
            u (s.1 0) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 2)) x := by sorry
