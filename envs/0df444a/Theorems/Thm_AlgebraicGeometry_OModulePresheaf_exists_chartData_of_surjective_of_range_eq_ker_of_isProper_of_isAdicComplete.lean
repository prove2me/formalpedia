-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/0ea46c0b-5a92-52f5-bcc5-8e9d724d485d
-- title:
--   Chart-wise module models for a formal extension of coherent sheaves
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal with $A$ $I$-adically complete, and $q : P \to \operatorname{Spec} A$ a proper morphism of schemes. Throughout, an `OModulePresheaf q` is a presheaf-like assignment $U \mapsto F(U)$ of modules over both $A$ and $\Gamma(P,U)$ (compatibly) with $A$-linear, $\Gamma$-semilinear restriction maps satisfying the usual identities; it is coherent when $F(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$, and quasicoherent when for every affine open $U$ and $f \in \Gamma(P,U)$ every section over $P.basicOpen f$ becomes, after multiplication by some $f^n$, a restriction from $U$, and every section over $U$ restricting to $0$ is killed by some $f^n$. An `AffHom` is a family of $A$-linear, $\Gamma$-semilinear maps on affine opens commuting with restriction. Given: coherent quasicoherent systems $(F_k)_{k \in \mathbb{N}}$ and $(E_k)_{k \in \mathbb{N}}$ with `AffHom`s $\varphi_k : F_{k+1} \to F_k$ and $\tau_k : E_{k+1} \to E_k$ that are surjective on each affine open with kernels $I^{k+1} F_{k+1}(U)$, resp. $I^{k+1} E_{k+1}(U)$; `AffHom`s $\varepsilon_k : F_k \to E_k$, surjective on affine opens and commuting with $\varphi_k, \tau_k$; a coherent quasicoherent $G_E$ with `AffHom`s $\psi^E_k : G_E \to E_k$, surjective on affine opens with kernel $I^{k+1} G_E(U)$ and compatible with the $\tau_k$; and a coherent quasicoherent $G_K$ with `AffHom`s $\lambda_k : G_K \to F_k$ compatible with the $\varphi_k$, with $\operatorname{range}(\lambda_k)_U = \ker(\varepsilon_k)_U$ on every affine open $U$, and satisfying an Artin–Rees shift: for each affine $U$ there is $c$ with $\ker(\lambda_{k+c})_U \subseteq I^{k+1} G_K(U)$ for all $k$. The conclusion asserts the existence of a finite linearly ordered affine open cover $K = (K.U i)_{i \in K.\iota}$ of $P$ together with, for each $i$ and each affine open $U \le K.U i$, a type $M_i(U)$ carrying $A$- and $\Gamma(P,U)$-module structures over the algebra structure induced by $q$, restriction maps $M_i(U) \to M_i(U')$ for $U' \le U$ that are $A$-linear, $\Gamma$-semilinear, reflexive and transitive, satisfy the same basic-open quasicoherence conditions as above, and make $M_i(U)$ a finite $\Gamma(P,U)$-module; $A$-linear, $\Gamma$-semilinear maps $\vartheta_{i,U} : G_K(U) \to M_i(U)$, $\theta^E_{i,U} : M_i(U) \to G_E(U)$ and $\theta^F_{i,k,U} : M_i(U) \to F_k(U)$, all commuting with restriction, with $\vartheta$ injective, $\theta^E$ surjective and $\operatorname{range}(\vartheta_{i,U}) = \ker(\theta^E_{i,U})$, and with $(\varphi_k)_U \circ \theta^F_{i,k+1,U} = \theta^F_{i,k,U}$, $\theta^F_{i,k,U} \circ \vartheta_{i,U} = (\lambda_k)_U$ and $(\varepsilon_k)_U \circ \theta^F_{i,k,U} = (\psi^E_k)_U \circ \theta^E_{i,U}$; and finally comparison maps $u_{i,j,W} : M_i(W) \to M_j(W)$ for affine $W \le K.U i$ with also $W \le K.U j$, which are $A$-linear bijections, $\Gamma(P,W)$-linear, natural in $W$, compatible with the $\vartheta$'s, and — this being the final assertion of the statement — satisfy $\theta^E_{j,W} \circ u_{i,j,W} = \theta^E_{i,W}$, so that each $u_{i,j,W}$ is an isomorphism of extensions of $G_E(W)$ by $G_K(W)$.
--
--   This is the chart-wise algebraisation step in the proof of Grothendieck's existence theorem for the extension of a coherent module by another over a proper scheme over a complete Noetherian base: the formal extension recorded by the towers $(F_k), (E_k)$ together with $G_E$ and $G_K$ is realised, on each member of a finite ordered affine cover, by an honest finitely generated module extension, the realisations agreeing up to canonical isomorphism of extensions over overlaps. Its conclusion forms the input data of [`AlgebraicGeometry.OModulePresheaf.exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_basisData_range_eq_ker_comp_eq_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete), the next stage of the same existence argument.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete
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
      LinearMap.ker ((lam (k + c)).app U) ≤ I ^ (k + 1) • (⊤ : Submodule A (GK.obj U.1))) :
    ∃ (K : P.OrderedAffineCover)
      (M : ∀ i : K.ι, {U : P.affineOpens // U.1 ≤ K.U i} → Type u)
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), AddCommGroup (M i U))
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module A (M i U))
      (iΓ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}), Module Γ(P, U.1.1) (M i U))
      (_ : ∀ (i : K.ι) (U : {U : P.affineOpens // U.1 ≤ K.U i}),
          letI := Scheme.TwoAffineOpenCover.algebraOfHom q U.1.1; IsScalarTower A Γ(P, U.1.1) (M i U))
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
          u i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x),
      ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θE j ⟨W.1, hj⟩ (u i j W hj x) = θE i W x := by sorry
