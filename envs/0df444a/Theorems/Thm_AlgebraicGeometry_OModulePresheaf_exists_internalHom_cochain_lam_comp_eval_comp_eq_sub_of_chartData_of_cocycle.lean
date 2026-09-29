-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle
-- name    : AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/cf3bcda0-8685-5cb7-a4db-c35955520254
-- title:
--   Čech 1-cochains measuring chart defects, given cocycle data
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal, and $q : P \to \operatorname{Spec} A$ a proper morphism of schemes. The data are: presheaves of modules $F_k$ over $q$ (each assigning to an open $U$ an $A$-module and a $\Gamma(P,U)$-module with compatible scalars, together with semilinear restriction maps), all coherent (finite over $\Gamma(P,U)$ on affine opens) and quasi-coherent in the sense of the stated basic-open conditions; maps $\varphi_k : F_{k+1} \to F_k$ given by $\Gamma$-linear maps on affine opens commuting with restriction, surjective on each affine open and with kernel $I^{k+1}\cdot F_{k+1}(U)$; further presheaves $E_k$ with maps $\varepsilon_k : F_k \to E_k$; coherent quasi-coherent $G_E$ with $\psi^E_k : G_E \to E_k$; coherent quasi-coherent $G_K$ with $\lambda_k : G_K \to F_k$ satisfying $\varphi_k \circ \lambda_{k+1} = \lambda_k$, $\operatorname{im} \lambda_k = \ker \varepsilon_k$ on affine opens, and, for each affine open $U$, some $c$ with $\ker \lambda_{k+c}(U) \subseteq I^{k+1} \cdot G_K(U)$ for all $k$. Let $K$ be an ordered affine cover of $P$ (a finite linearly ordered family of affine opens with supremum $\top$). For each chart index $i$ and each affine open $W \le K.U\,i$ there is given an $A$- and $\Gamma(P,W)$-module $M_i(W)$ with compatible scalars, $A$-linear restrictions $\mathrm{res}$, and $A$-linear maps $\vartheta^i : G_K(W) \to M_i(W)$, $\theta^{E,i} : M_i(W) \to G_E(W)$, $\theta^{F,i}_k : M_i(W) \to F_k(W)$, all $\Gamma(P,W)$-linear, with $\theta^{E,i}$ and $\theta^{F,i}_k$ compatible with restriction, $\operatorname{im}\vartheta^i = \ker \theta^{E,i}$, $\theta^{E,i}$ surjective, $\varphi_k \circ \theta^{F,i}_{k+1} = \theta^{F,i}_k$, $\theta^{F,i}_k \circ \vartheta^i = \lambda_k$ and $\varepsilon_k \circ \theta^{F,i}_k = \psi^E_k \circ \theta^{E,i}$. Finally, for $W$ affine with $W \le K.U\,i$ and $W \le K.U\,j$ there are $A$-linear overlap maps $u_{ij} : M_i(W) \to M_j(W)$, assumed $\Gamma(P,W)$-linear, compatible with $\mathrm{res}$, with $u_{ij} \circ \vartheta^i = \vartheta^j$, $\theta^{E,j} \circ u_{ij} = \theta^{E,i}$, and satisfying the cocycle identity $u_{jl} \circ u_{ij} = u_{il}$. The conclusion asserts the existence of a sequence $t_n$ of Čech $1$-cochains of the internal Hom presheaf $\mathcal{H}om(G_E,G_K)$ for $K$ — so $t_n$ assigns to each strictly increasing $s : \mathrm{Fin}\,2 \to K.\iota$ a family, indexed by the affine opens $W$ contained in $K.U\,s_0 \cap K.U\,s_1$, of $\Gamma(P,W)$-linear maps $G_E(W) \to G_K(W)$ compatible with restriction — such that: for all $n$, $s$, such $W$ and all $x \in M_{s_0}(W)$, $\lambda_n\bigl(t_n(s)_W(\theta^{E,s_0}(x))\bigr) = \theta^{F,s_1}_n(u_{s_0 s_1}(x)) - \theta^{F,s_0}_n(x)$; the Čech differential $d^1 t_n$ lies in $I^{n+1}$ times the whole module of $2$-cochains; and $t_{n+1} - t_n$ lies in $I^{n+1}$ times the whole module of $1$-cochains.
--
--   This is the first construction step in the comparison of $\mathrm{Ext}^1$ with its $I$-adic completion over a proper base: the failure of the chart-wise comparison maps $\theta^{F,i}_n$ to agree on overlaps is realised, after composing with $\lambda_n$, by an $I$-adically Cauchy sequence of Čech $1$-cochains of $\mathcal{H}om(G_E,G_K)$ whose coboundaries are $I$-adically small. It is the version of `exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData` in which the overlap maps are assumed to satisfy the cocycle condition, and it feeds into `exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete`, where the limit cochain is turned into an honest Čech cocycle.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_OModulePresheafInternalHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {P : Scheme.{u}} (q : P ⟶ Spec (CommRingCat.of A)) [IsProper q]
    (F : ℕ → OModulePresheaf q) (hFc : ∀ k, (F k).IsCoherent) (hFq : ∀ k, (F k).IsQuasicoherent)
    (φ : ∀ k, OModulePresheaf.AffHom (F (k + 1)) (F k))
    (hφs : ∀ (k : ℕ) (U : P.affineOpens), Function.Surjective ((φ k).app U))
    (hφk : ∀ (k : ℕ) (U : P.affineOpens),
      LinearMap.ker ((φ k).app U) = I ^ (k + 1) • (⊤ : Submodule A ((F (k + 1)).obj U.1)))
    (E : ℕ → OModulePresheaf q)
    (ε : ∀ k, OModulePresheaf.AffHom (F k) (E k))
    (GE : OModulePresheaf q) (hGEc : GE.IsCoherent) (hGEq : GE.IsQuasicoherent)
    (ψE : ∀ k, OModulePresheaf.AffHom GE (E k))
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
    (ϑ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), GK.obj U.1.1 →ₗ[A] M i U)
    (θE : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] GE.obj U.1.1)
    (θF : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1)
    (hϑs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : GK.obj U.1.1), ϑ i U (a • x) = a • ϑ i U x)
    (hθEs : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U), θE i U (a • x) = a • θE i U x)
    (hθFs : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF i k U (a • x) = a • θF i k U x)
    (hθEn : ∀ (i : K.ι) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θE i U' (res i h x) = GE.res h (θE i U x))
    (hθFn : ∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF i k U' (res i h x) = (F k).res h (θF i k U x))
    (hexact : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), LinearMap.range (ϑ i U) = LinearMap.ker (θE i U))
    (hsurj : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Function.Surjective (θE i U))
    (hc1 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF i (k + 1) U = θF i k U)
    (hc2 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF i k U ∘ₗ ϑ i U = (lam k).app U.1)
    (hc3 : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF i k U = (ψE k).app U.1 ∘ₗ θE i U)

    (u : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩)
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
    :
    ∃ t : ℕ → (OModulePresheaf.internalHom GE GK).cochain K 1,

      (∀ (n : ℕ) (s : K.Idx 1) (W : OModulePresheaf.AffBelow (K.inter s)) (x : M (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩),
        (lam n).app W.1 (OModulePresheaf.internalHom.eval GE GK W.1 W.2 (t n s) (θE (s.1 0) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x)) =
          θF (s.1 1) n ⟨W.1, W.2.trans (K.inter_le s 1)⟩ (u (s.1 0) (s.1 1) ⟨W.1, W.2.trans (K.inter_le s 0)⟩ (W.2.trans (K.inter_le s 1)) x) - θF (s.1 0) n ⟨W.1, W.2.trans (K.inter_le s 0)⟩ x) ∧

      (∀ n : ℕ, (OModulePresheaf.internalHom GE GK).d K 1 (t n) ∈
        I ^ (n + 1) • (⊤ : Submodule A ((OModulePresheaf.internalHom GE GK).cochain K 2))) ∧

      (∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A ((OModulePresheaf.internalHom GE GK).cochain K 1))) := by sorry
