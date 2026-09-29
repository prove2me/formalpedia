-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData
-- name    : AlgebraicGeometry.OModulePresheaf.mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/5fc23de9-9913-5f5c-a2ef-4123c5534cc2
-- title:
--   Chartwise obstruction 2-cochain lies in Iⁿ⁺¹C²+dC¹
-- statement:
--   Throughout, $A$ is a Noetherian commutative ring, $I\subseteq A$ an ideal for which $A$ is $I$-adically complete, and $q\colon P\to\operatorname{Spec}A$ a proper morphism of schemes. The objects carrying the data are `OModulePresheaf q`'s: assignments $U\mapsto F(U)$ of an $A$-module and a $\Gamma(P,U)$-module to each open $U$ of $P$ (the two actions related by the scalar tower over the $A$-algebra structure on $\Gamma(P,U)$ coming from $q$), together with $A$-linear restrictions $F(U')\to F(U)$ for $U\le U'$ that are semilinear for the restriction maps of $\mathcal O_P$ and satisfy the identity and transitivity laws. For such an object, `IsCoherent` says that $F(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and `IsQuasicoherent` says that for every affine open $U$ and every $f\in\Gamma(P,U)$ each section over the basic open $D(f)$ becomes, after multiplication by some power of $f$, the restriction of a section over $U$, and each section over $U$ restricting to $0$ on $D(f)$ is annihilated by some power of $f$. An `AffHom F G` is a family of $A$-linear maps $F(U)\to G(U)$ indexed by the affine opens $U$, each $\Gamma(P,U)$-linear, and commuting with restriction between affine opens.
--
--   The first group of data is a formal system on $P$. There are `OModulePresheaf q`'s $F_k$ ($k\in\mathbb N$), coherent (`hFc`) and quasicoherent (`hFq`), with maps $\varphi_k\colon F_{k+1}\to F_k$ that on every affine open $U$ are surjective (`hφs`) with kernel $I^{k+1}F_{k+1}(U)$ (`hφk`); a second such system $E_k$, coherent (`hEc`) and quasicoherent (`hEq`), with maps $\tau_k\colon E_{k+1}\to E_k$, surjective on affine opens (`hτs`) with kernel $I^{k+1}E_{k+1}(U)$ (`hτk`); and maps $\varepsilon_k\colon F_k\to E_k$, surjective on affine opens (`hεs`), compatible with the two systems in the sense that $\tau_k\circ\varepsilon_{k+1}=\varepsilon_k\circ\varphi_k$ on each affine open (`hεc`).
--
--   Next, two further objects with their approximations. $GE$ is coherent (`hGEc`) and quasicoherent (`hGEq`), and comes with maps $\psi^E_k\colon GE\to E_k$ which on each affine open $U$ are surjective (`hψEs`), have kernel $I^{k+1}GE(U)$ (`hψEk`), and satisfy $\tau_k\circ\psi^E_{k+1}=\psi^E_k$ (`hψEc`). $GK$ is coherent (`hGKc`) and quasicoherent (`hGKq`), and comes with maps $\lambda_k\colon GK\to F_k$ satisfying $\varphi_k\circ\lambda_{k+1}=\lambda_k$ (`hlamc`), with image on each affine open $U$ equal to the kernel of $\varepsilon_k$ on $U$ (`hlamr`), and subject to the Artin–Rees type control `hlami`: for every affine open $U$ there is $c\in\mathbb N$ such that $\ker(\lambda_{k+c})_U\subseteq I^{k+1}GK(U)$ for all $k$.
--
--   The covering data is an `OrderedAffineCover` $K$ of $P$: a finite linearly ordered index type $\iota$ and affine opens $U_i$ with $\bigsqcup_i U_i=\top$. For $i\in\iota$ and each affine open $U\le U_i$ there is a module $M_i(U)$, an $A$-module and a $\Gamma(P,U)$-module with the scalar tower over $A$, together with restriction maps $\mathrm{res}_i$ for $U'\le U$ below $U_i$, which are $A$-linear, semilinear for the restriction of $\mathcal O_P$ (`res_smul`), and satisfy $\mathrm{res}_i(\mathrm{id})=\mathrm{id}$ (`res_refl`) and transitivity (`res_comp`). The hypothesis `hqc` imposes quasicoherence of each $M_i$ in the above shape: for affine opens $U,U_f\le U_i$ and $f\in\Gamma(P,U)$ with $U_f=D(f)$, every element of $M_i(U_f)$ is, after multiplication by some power of $f$, the restriction of an element of $M_i(U)$, and every element of $M_i(U)$ restricting to $0$ on $U_f$ is killed by a power of $f$; `hfg` requires $M_i(U)$ to be a finite $\Gamma(P,U)$-module.
--
--   The comparison maps are $A$-linear maps $\vartheta^i_U\colon GK(U)\to M_i(U)$, $\theta^{E,i}_U\colon M_i(U)\to GE(U)$ and $\theta^{F,i,k}_U\colon M_i(U)\to F_k(U)$, for $i\in\iota$ and affine $U\le U_i$. They are $\Gamma(P,U)$-linear (`hϑs`, `hθEs`, `hθFs`) and natural for restriction to smaller affine opens below $U_i$ (`hϑn`, `hθEn`, `hθFn`). Exactness is imposed by `hexact` (the image of $\vartheta^i_U$ is the kernel of $\theta^{E,i}_U$), `hsurj` ($\theta^{E,i}_U$ is surjective) and `hϑi` ($\vartheta^i_U$ is injective); thus $M_i$ is an extension of $GE$ by $GK$ over each affine open below $U_i$. The compatibilities with the formal system are $\varphi_k\circ\theta^{F,i,k+1}_U=\theta^{F,i,k}_U$ (`hc1`), $\theta^{F,i,k}_U\circ\vartheta^i_U=(\lambda_k)_U$ (`hc2`) and $(\varepsilon_k)_U\circ\theta^{F,i,k}_U=(\psi^E_k)_U\circ\theta^{E,i}_U$ (`hc3`).
--
--   Finally, for $i,j\in\iota$ and an affine open $W\le U_i$ with also $W\le U_j$ there are $A$-linear transition maps $u_{ij,W}\colon M_i(W)\to M_j(W)$, which are bijective (`hub`), $\Gamma(P,W)$-linear (`hus`), natural for restriction to smaller affine opens (`hun`), and compatible with the extension structure: $u_{ij,W}\circ\vartheta^i_W=\vartheta^j_W$ (`huϑ`) and $\theta^{E,j}_W\circ u_{ij,W}=\theta^{E,i}_W$ (`huθE`).
--
--   Let $g$ be a Čech $2$-cochain of the internal Hom presheaf $\mathcal Hom(GE,GK)=$ `internalHom GE GK`, i.e. for every strictly monotone $s\colon\{0,1,2\}\to\iota$ an element $g_s$ of the module of sections over $\bigsqcap_{j}U_{s(j)}$, such a section being by definition a family assigning to each affine open $W$ below that intersection a $\Gamma(P,W)$-linear map $GE(W)\to GK(W)$, compatibly with restriction. The hypothesis `hg` states that $g$ computes the failure of the transition maps to satisfy the cocycle condition: for every such $s$, writing $i=s(0)$, $j=s(1)$, $l=s(2)$, every affine open $W$ contained in $U_i\cap U_j\cap U_l$ and every $x\in M_i(W)$ satisfy
--   $$\vartheta^{l}_W\bigl((g_s)_W(\theta^{E,i}_W x)\bigr)=u_{jl,W}\bigl(u_{ij,W}x\bigr)-u_{il,W}x .$$
--
--   The conclusion is that for every $n\in\mathbb N$ the cochain $g$ lies in the join (equivalently, the sum) of the submodule $I^{n+1}\cdot C^2(K,\mathcal Hom(GE,GK))$ of the full $A$-module of $2$-cochains and the image of the degree-$1$ Čech differential `(internalHom GE GK).d K 1` from $1$-cochains to $2$-cochains; that is, $g$ is a coboundary modulo $I^{n+1}$ cochains, for every $n$.
--
--   This is the main approximation step in the Grothendieck existence/algebraisation argument for extensions given chartwise: the $2$-cochain measuring the failure of the chartwise extensions $M_i$ of $GE$ by $GK$ to glue is shown to be a coboundary to any prescribed $I$-adic precision, using the Artin–Rees control on $\ker\lambda_k$ and coherence of the internal Hom. It feeds into [`AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_cocycle_of_chartData_of_isProper_of_isAdicComplete), where the successive approximations are assembled over the $I$-adically complete base.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.mem_pow_smul_sup_range_d_of_forall_eq_comp_sub_of_chartData
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
    (n : ℕ) :
    g ∈ I ^ (n + 1) • (⊤ : Submodule A ((OModulePresheaf.internalHom GE GK).cochain K 2)) ⊔
      LinearMap.range ((OModulePresheaf.internalHom GE GK).d K 1) := by sorry
