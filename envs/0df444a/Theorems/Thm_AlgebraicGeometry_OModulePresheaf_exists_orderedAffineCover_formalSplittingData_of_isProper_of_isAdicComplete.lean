-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.OModulePresheaf.exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.683218+00:00
-- url     : https://prove2.me/theorems/23e5b8c4-f5bb-59d2-a298-a0ec001529d2
-- title:
--   Formal splitting data on an ordered affine cover
-- statement:
--   Let $A$ be a Noetherian commutative ring, $I \subseteq A$ an ideal with $A$ $I$-adically complete, and let $q : P \to \operatorname{Spec} A$ be a proper morphism of schemes. The data are: two families $F, E : \mathbb{N} \to$ `OModulePresheaf q` (assignments of an $A$-module and $\Gamma(P,U)$-module, compatibly, to each open $U$, with restriction maps), each member coherent (module-finite over $\Gamma(P,U)$ on affine opens) and quasi-coherent (the basic-open conditions of `IsQuasicoherent`); transition maps $\varphi_k : F(k+1) \to F(k)$ and $\tau_k : E(k+1) \to E(k)$, which on each affine open $U$ are surjective with kernel $I^{k+1} \cdot F(k+1)(U)$, resp. $I^{k+1} \cdot E(k+1)(U)$; maps $\varepsilon_k : F(k) \to E(k)$, surjective on affine opens and with $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$; a coherent quasi-coherent $G_E$ with $\psi^E_k : G_E \to E(k)$, surjective on affine opens with kernel $I^{k+1} \cdot G_E(U)$ and $\tau_k \circ \psi^E_{k+1} = \psi^E_k$; a coherent quasi-coherent $G_K$ with $\lambda_k : G_K \to F(k)$ satisfying $\varphi_k \circ \lambda_{k+1} = \lambda_k$, $\operatorname{range}(\lambda_k) = \ker(\varepsilon_k)$ on every affine open $U$, and an Artin–Rees bound: for each affine $U$ there is $c$ with $\ker(\lambda_{k+c}(U)) \subseteq I^{k+1} \cdot G_K(U)$ for all $k$. Finally a coherent quasi-coherent $X$ together with chart isomorphisms $\varepsilon^X_{W,r,p} : X(W) \cong \operatorname{Hom}_{\Gamma(P,W)}(\ker p, G_K(W)) / \{\text{homs extending to } \Gamma(P,W)^r\}$ for every affine $W$ and every surjection $p : \Gamma(P,W)^r \to G_E(W)$, and a compatibility hypothesis: whenever $W' \le W$, $p, p'$ are such surjections, $g : \Gamma(P,W)^r \to \Gamma(P,W')^{r'}$ is additive and semilinear over the restriction map with $p' \circ g = \operatorname{res} \circ p$, and $\delta, \delta'$ are homs out of $\ker p$, $\ker p'$ with $\delta' \circ g = \operatorname{res} \circ \delta$ on $\ker p$, then restriction carries the class of $\delta$ to the class of $\delta'$. The conclusion asserts the existence of an ordered affine cover $K$ of $P$ (a finite linearly ordered index set $\iota$ and affine opens $U_i$ with $\bigsqcup_i U_i = \top$), ranks $r_i$, surjections $\mathrm{pr}_i : \Gamma(P,U_i)^{r_i} \to G_E(U_i)$, maps $\ell_{i,n} : \Gamma(P,U_i)^{r_i} \to F(n)(U_i)$, maps $\delta_{i,n} : \ker(\mathrm{pr}_i) \to G_K(U_i)$, and $0$-cochains $t_n$ of $X$ on $K$, such that $\varepsilon_n \circ \ell_{i,n} = \psi^E_n \circ \mathrm{pr}_i$; $\varphi_n \circ \ell_{i,n+1} = \ell_{i,n}$; $\lambda_n \circ \delta_{i,n}$ agrees with $\ell_{i,n}$ on $\ker(\mathrm{pr}_i)$; $\delta_{i,n+1} - \delta_{i,n}$ lies in the $(n+1)$st power of the image of $I$ in $\Gamma(P,U_i)$ times $\operatorname{Hom}(\ker \mathrm{pr}_i, G_K(U_i))$; $t_n$ is, at each index $s$, the restriction to $\bigcap s$ of $(\varepsilon^X)^{-1}$ of the class of $\delta_{s(0),n}$; and $d^0 t_n \in I^{n+1} \cdot \check{C}^1(K, X)$, $t_{n+1} - t_n \in I^{n+1} \cdot \check{C}^0(K, X)$ for all $n$.
--
--   This is the globalisation step in the formal-existence package: from an $I$-adic system of coherent module data on a proper $A$-scheme, together with algebraisations $G_E$, $G_K$ of the quotient and kernel families and an $\operatorname{Ext}^1$-chart presheaf $X$, it produces a single finite ordered affine cover carrying levelwise presentations, compatible lifts, congruent $\operatorname{Hom}$-representatives, and Čech $0$-cochains whose coboundaries and successive differences are $I$-adically small. It is used by [`AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_chartData_of_surjective_of_range_eq_ker_of_isProper_of_isAdicComplete).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom
import Definitions.Def_AlgebraicGeometry_TwoAffineOpenCover

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_orderedAffineCover_formalSplittingData_of_isProper_of_isAdicComplete
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

    (X : OModulePresheaf q) (hXc : X.IsCoherent) (hXq : X.IsQuasicoherent)
    (εX : ∀ (W : P.affineOpens) (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1), Function.Surjective p →
        (X.obj W.1 ≃ₗ[Γ(P, W.1)]
          ((↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) ⧸
            LinearMap.range (LinearMap.lcomp (Γ(P, W.1)) (GK.obj W.1) (LinearMap.ker p).subtype))))
    (hXf : ∀ (W W' : P.affineOpens) (h : W'.1 ≤ W.1)
        (r : ℕ) (p : (Fin r → Γ(P, W.1)) →ₗ[Γ(P, W.1)] GE.obj W.1) (hp : Function.Surjective p)
        (r' : ℕ) (p' : (Fin r' → Γ(P, W'.1)) →ₗ[Γ(P, W'.1)] GE.obj W'.1) (hp' : Function.Surjective p')
        (g : (Fin r → Γ(P, W.1)) →+ (Fin r' → Γ(P, W'.1)))
        (_hg : ∀ (a : Γ(P, W.1)) (v : Fin r → Γ(P, W.1)), g (a • v) = (P.presheaf.map (homOfLE h).op).hom a • g v)
        (hgp : ∀ v : Fin r → Γ(P, W.1), p' (g v) = GE.res h (p v))
        (δ : ↥(LinearMap.ker p) →ₗ[Γ(P, W.1)] GK.obj W.1) (δ' : ↥(LinearMap.ker p') →ₗ[Γ(P, W'.1)] GK.obj W'.1)
        (hδ : ∀ s : ↥(LinearMap.ker p),
          δ' ⟨g s.1, by rw [LinearMap.mem_ker, hgp, (LinearMap.mem_ker.mp s.2), map_zero]⟩ = GK.res h (δ s)),
        X.res h ((εX W r p hp).symm (Submodule.Quotient.mk δ)) = (εX W' r' p' hp').symm (Submodule.Quotient.mk δ')) :
    ∃ (K : P.OrderedAffineCover) (rk : K.ι → ℕ)
      (pr : ∀ i : K.ι, (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] GE.obj (K.U i))
      (hpr : ∀ i : K.ι, Function.Surjective (pr i))
      (ℓ : ∀ (i : K.ι) (n : ℕ), (Fin (rk i) → Γ(P, K.U i)) →ₗ[Γ(P, K.U i)] (F n).obj (K.U i))
      (δs : ∀ (i : K.ι) (n : ℕ), ↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i))
      (t : ℕ → X.cochain K 0),

      (∀ (i : K.ι) (n : ℕ) (v : Fin (rk i) → Γ(P, K.U i)),
        (ε n).app ⟨K.U i, K.isAffineOpen i⟩ (ℓ i n v) = (ψE n).app ⟨K.U i, K.isAffineOpen i⟩ (pr i v)) ∧

      (∀ (i : K.ι) (n : ℕ) (v : Fin (rk i) → Γ(P, K.U i)),
        (φ n).app ⟨K.U i, K.isAffineOpen i⟩ (ℓ i (n + 1) v) = ℓ i n v) ∧

      (∀ (i : K.ι) (n : ℕ) (s : ↥(LinearMap.ker (pr i))),
        (lam n).app ⟨K.U i, K.isAffineOpen i⟩ (δs i n s) = ℓ i n (s : Fin (rk i) → Γ(P, K.U i))) ∧

      (∀ (i : K.ι) (n : ℕ),
        δs i (n + 1) - δs i n ∈
          (I.map (Scheme.TwoAffineOpenCover.algebraOfHom q (K.U i)).algebraMap) ^ (n + 1) •
            (⊤ : Submodule Γ(P, K.U i) (↥(LinearMap.ker (pr i)) →ₗ[Γ(P, K.U i)] GK.obj (K.U i)))) ∧

      (∀ (n : ℕ) (s : K.Idx 0),
        t n s = X.res (K.inter_le s 0)
          ((εX ⟨K.U (s.1 0), K.isAffineOpen (s.1 0)⟩ (rk (s.1 0)) (pr (s.1 0)) (hpr (s.1 0))).symm (Submodule.Quotient.mk (δs (s.1 0) n)))) ∧

      (∀ n : ℕ, X.d K 0 (t n) ∈ I ^ (n + 1) • (⊤ : Submodule A (X.cochain K 1))) ∧

      (∀ n : ℕ, t (n + 1) - t n ∈ I ^ (n + 1) • (⊤ : Submodule A (X.cochain K 0))) := by sorry
