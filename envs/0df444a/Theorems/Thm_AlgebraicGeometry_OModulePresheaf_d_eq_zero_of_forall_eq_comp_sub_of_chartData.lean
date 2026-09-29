-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_d_eq_zero_of_forall_eq_comp_sub_of_chartData
-- name    : AlgebraicGeometry.OModulePresheaf.d_eq_zero_of_forall_eq_comp_sub_of_chartData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/d1ff33e3-ae31-510a-a7db-1c24ed17a106
-- title:
--   Discrepancy 2-cochain of the chart isomorphisms is a Čech cocycle
-- statement:
--   Throughout, $A$ is a commutative Noetherian ring in universe $u$, $I \subseteq A$ an ideal such that $A$ is $I$-adically complete, $P$ a scheme and $q : P \to \operatorname{Spec} A$ a proper morphism. For such a $q$, an `OModulePresheaf q` consists of $A$-modules $\mathcal F(U)$ indexed by the opens $U$ of $P$, each carrying in addition a $\Gamma(P,U)$-module structure compatible (as a scalar tower) with the $A$-algebra structure on $\Gamma(P,U)$ coming from $q$, together with $A$-linear restriction maps $\mathcal F(U') \to \mathcal F(U)$ for $U \le U'$ that are semilinear over restriction of functions, reflexive and transitive. For such an object, `IsCoherent` asserts that $\mathcal F(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and `IsQuasicoherent` asserts that for every affine open $U$ and every $f \in \Gamma(P,U)$, each section over the basic open $P.\mathrm{basicOpen}\, f$ becomes the restriction of a section over $U$ after multiplication by a suitable power of $f$, and each section over $U$ restricting to $0$ on that basic open is annihilated by a power of $f$. An `AffHom` between two such presheaves is a family of $A$-linear maps on the affine opens, semilinear over $\Gamma$ and commuting with restriction.
--
--   The data are as follows. A tower $F : \mathbb N \to$ `OModulePresheaf q` with all $F_k$ coherent (`hFc`) and quasi-coherent (`hFq`), and maps $\varphi_k \in$ `AffHom` $(F_{k+1}, F_k)$ which on every affine open $U$ are surjective (`hφs`) with kernel $I^{k+1} F_{k+1}(U)$ (`hφk`). A second such tower $E$, coherent (`hEc`) and quasi-coherent (`hEq`), with maps $\tau_k : E_{k+1} \to E_k$ surjective on affine opens (`hτs`) and with kernel $I^{k+1} E_{k+1}(U)$ (`hτk`). Maps $\varepsilon_k : F_k \to E_k$, surjective on affine opens (`hεs`) and commuting with the towers in the sense $(\tau_k)_U \circ (\varepsilon_{k+1})_U = (\varepsilon_k)_U \circ (\varphi_k)_U$ (`hεc`). A coherent (`hGEc`) and quasi-coherent (`hGEq`) presheaf $\mathcal G_E$ with maps $\psi^E_k : \mathcal G_E \to E_k$ which on affine opens are surjective (`hψEs`), have kernel $I^{k+1}\mathcal G_E(U)$ (`hψEk`) and satisfy $(\tau_k)_U \circ (\psi^E_{k+1})_U = (\psi^E_k)_U$ (`hψEc`). A coherent (`hGKc`) and quasi-coherent (`hGKq`) presheaf $\mathcal G_K$ with maps $\lambda_k : \mathcal G_K \to F_k$ satisfying $(\varphi_k)_U \circ (\lambda_{k+1})_U = (\lambda_k)_U$ (`hlamc`), with $\operatorname{range}(\lambda_k)_U = \ker(\varepsilon_k)_U$ on every affine open (`hlamr`), and such that for every affine open $U$ there is $c \in \mathbb N$ with $\ker(\lambda_{k+c})_U \le I^{k+1}\mathcal G_K(U)$ for all $k$ (`hlami`).
--
--   Next, $K$ is an `OrderedAffineCover` of $P$: a finite, linearly ordered index type $K.\iota$ together with opens $K.U_i$, each affine, whose supremum is $\top$. The chart data consist of types $M_i(U)$ for $i \in K.\iota$ and $U$ an affine open contained in $K.U_i$, each an abelian group, an $A$-module and a $\Gamma(P,U)$-module forming a scalar tower over the algebra structure induced by $q$ (these typeclass assumptions are summarised here), with $A$-linear restriction maps `res` that are semilinear over restriction of functions (`res_smul`), reflexive (`res_refl`) and transitive (`res_comp`); the hypothesis `hqc` imposes, for each $i$, each $U$ and each $Ug$ equal to the basic open of some $g \in \Gamma(P,U)$, the two quasi-coherence clauses for `res` (every element of $M_i(Ug)$ is a power of $g$ times the restriction of an element of $M_i(U)$, and an element of $M_i(U)$ restricting to $0$ is annihilated by a power of $g$), and `hfg` requires $M_i(U)$ to be a finite $\Gamma(P,U)$-module.
--
--   The chart data are tied to the presheaves by $A$-linear maps $\vartheta_{i,U} : \mathcal G_K(U) \to M_i(U)$, $\theta^E_{i,U} : M_i(U) \to \mathcal G_E(U)$ and $\theta^F_{i,k,U} : M_i(U) \to F_k(U)$, all $\Gamma(P,U)$-linear (`hϑs`, `hθEs`, `hθFs`) and compatible with restriction (`hϑn`, `hθEn`, `hθFn`), with $\operatorname{range}\vartheta_{i,U} = \ker\theta^E_{i,U}$ (`hexact`), $\theta^E_{i,U}$ surjective (`hsurj`), $\vartheta_{i,U}$ injective (`hϑi`), and the compatibilities $(\varphi_k)_U \circ \theta^F_{i,k+1,U} = \theta^F_{i,k,U}$ (`hc1`), $\theta^F_{i,k,U} \circ \vartheta_{i,U} = (\lambda_k)_U$ (`hc2`) and $(\varepsilon_k)_U \circ \theta^F_{i,k,U} = (\psi^E_k)_U \circ \theta^E_{i,U}$ (`hc3`).
--
--   Finally, for indices $i, j$ and an affine open $W \le K.U_i$ with also $W \le K.U_j$, there are $A$-linear transition maps $u_{i j, W} : M_i(W) \to M_j(W)$ which are bijective (`hub`), $\Gamma(P,W)$-linear (`hus`), compatible with restriction (`hun`), and satisfy $u_{ij,W} \circ \vartheta_{i,W} = \vartheta_{j,W}$ (`huϑ`) and $\theta^E_{j,W} \circ u_{ij,W} = \theta^E_{i,W}$ (`huθE`).
--
--   The cochain in question is $g$, a degree-$2$ Čech cochain for $K$ with values in `internalHom` $\mathcal G_E\ \mathcal G_K$: for each strictly increasing triple $s = (s_0 < s_1 < s_2)$ in $K.\iota$, a section over $K.\mathrm{inter}\,s = K.U_{s_0} \cap K.U_{s_1} \cap K.U_{s_2}$ of the internal Hom presheaf, i.e. a family $(g_s)_W : \mathcal G_E(W) \to \mathcal G_K(W)$ of $A$-linear maps indexed by the affine opens $W \le K.\mathrm{inter}\,s$, each $\Gamma(P,W)$-linear and compatible with restriction. The hypothesis `hg` states that $g$ measures the failure of the transition maps to compose: for every such $s$, every affine open $W \le K.\mathrm{inter}\,s$ and every $x \in M_{s_0}(W)$,
--   $$\vartheta_{s_2,W}\bigl((g_s)_W(\theta^E_{s_0,W}\,x)\bigr) = u_{s_1 s_2, W}\bigl(u_{s_0 s_1, W}\,x\bigr) - u_{s_0 s_2, W}\,x .$$
--
--   The conclusion is that the degree-$2$ Čech differential of $g$ for the cover $K$, formed in the presheaf `internalHom` $\mathcal G_E\ \mathcal G_K$, vanishes: `(OModulePresheaf.internalHom GE GK).d K 2 g = 0`. Equivalently, $g$ is a Čech $2$-cocycle.
--
--   The statement records that the discrepancy cochain attached to the transition bijections between charts — the obstruction to the maps $u_{ij}$ composing strictly — is a Čech $2$-cocycle with values in the internal Hom presheaf $\mathcal{H}om(\mathcal G_E,\mathcal G_K)$, the point being that the identity defining $g$ determines it uniquely, since $\vartheta$ is injective and $\theta^E$ surjective. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete) in the gluing argument for coherent chart data over a proper scheme with adically complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_d_eq_zero_of_forall_eq_comp_sub_of_chartData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.d_eq_zero_of_forall_eq_comp_sub_of_chartData
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
    (g : (OModulePresheaf.internalHom GE GK).cochain K 2)
    (hg : ∀ (s : K.Idx 2) (W : {U : P.affineOpens // U.1 ≤ K.inter s})
        (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩),
        ϑ (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 2)⟩ ((g s).1 W (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
          u (s.1 1) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (W.2.trans (K.inter_le s 2))
              (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) -
            u (s.1 0) (s.1 2) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 2)) x)
    :
    (OModulePresheaf.internalHom GE GK).d K 2 g = 0 := by sorry
