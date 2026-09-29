-- Prove2me | Theorems.Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete
-- name    : AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:42.268945+00:00
-- url     : https://prove2.me/theorems/1aa9cb0f-c5f2-5fe6-af6e-9cefc3cfba2d
-- title:
--   Twisting chart comparison maps compatible with a Čech 1-cocycle
-- statement:
--   Throughout, $A$ is a Noetherian commutative ring, $I \subseteq A$ an ideal with $A$ $I$-adically complete, and $q : P \to \operatorname{Spec} A$ a proper morphism of schemes. All sheaf-like objects are `OModulePresheaf q`: such an object $F$ assigns to every open $U \subseteq P$ an $A$-module $F(U)$ carrying in addition a $\Gamma(P,U)$-module structure forming a scalar tower over $A$ (via the $A$-algebra structure on $\Gamma(P,U)$ coming from $q$), together with $A$-linear restriction maps $F(U') \to F(U)$ for $U \le U'$ that are semilinear over restriction of sections and satisfy the reflexivity and transitivity identities. `IsCoherent` means that $F(U)$ is a finite $\Gamma(P,U)$-module for every affine open $U$; `IsQuasicoherent` means that for every affine open $U$ and $f \in \Gamma(P,U)$ each element of $F(P_f)$ becomes, after multiplication by some power of $f$, the restriction of an element of $F(U)$, and each element of $F(U)$ restricting to $0$ on $P_f$ is annihilated by a power of $f$. An `AffHom F G` is a family of maps $F(U) \to G(U)$ indexed by the affine opens $U$, each $\Gamma(P,U)$-linear, and natural for restrictions between affine opens.
--
--   The formal data are as follows. A system $(F_k)_{k \in \mathbb{N}}$ of coherent and quasicoherent objects (`hFc`, `hFq`) with transition maps $\varphi_k : F_{k+1} \to F_k$ which on every affine open are surjective (`hφs`) with kernel $I^{k+1} F_{k+1}(U)$ (`hφk`); a second such system $(E_k)$ with $\tau_k : E_{k+1} \to E_k$ (`hEc`, `hEq`, `hτs`, `hτk`, the same conditions); maps $\varepsilon_k : F_k \to E_k$ that are surjective on affine opens (`hεs`) and satisfy $\tau_k \circ \varepsilon_{k+1} = \varepsilon_k \circ \varphi_k$ there (`hεc`); a coherent quasicoherent $GE$ (`hGEc`, `hGEq`) with maps $\psi^E_k : GE \to E_k$, surjective on affine opens (`hψEs`), with kernel $I^{k+1} GE(U)$ (`hψEk`) and satisfying $\tau_k \circ \psi^E_{k+1} = \psi^E_k$ (`hψEc`); and a coherent quasicoherent $GK$ (`hGKc`, `hGKq`) with maps $\lambda_k : GK \to F_k$ satisfying $\varphi_k \circ \lambda_{k+1} = \lambda_k$ (`hlamc`), with image on each affine open equal to $\ker (\varepsilon_k)_U$ (`hlamr`), and such that for every affine open $U$ there is $c \in \mathbb{N}$ with $\ker (\lambda_{k+c})_U \subseteq I^{k+1} GK(U)$ for all $k$ (`hlami`).
--
--   The geometric index data is an `OrderedAffineCover` $K$ of $P$: a finite linearly ordered index type $K.\iota$ together with opens $K.U_i$ that are affine and whose supremum is $\top$. The chart data consists of, for each $i \in K.\iota$ and each affine open $U$ of $P$ with $U \le K.U_i$, a type $M_i(U)$ of universe $u$, with the typeclass data of an $A$-module and a $\Gamma(P,U)$-module forming a scalar tower over $A$ (the $\Gamma$-module instances being named `iΓ`), together with: restriction maps $\operatorname{res}_i^h : M_i(U) \to M_i(U')$, $A$-linear, for $U' \le U$ inside $K.U_i$, semilinear over restriction of sections (`res_smul`), reflexive (`res_refl`) and transitive (`res_comp`); a quasicoherence condition `hqc` on basic opens ($Ug = P_g$ for $g \in \Gamma(P,U)$: every element of $M_i(Ug)$ is $g^n$ times the restriction of an element of $M_i(U)$, and an element of $M_i(U)$ restricting to $0$ is killed by a power of $g$); and finiteness of $M_i(U)$ over $\Gamma(P,U)$ (`hfg`).
--
--   The comparison data consists of $A$-linear maps $\vartheta^i_U : GK(U) \to M_i(U)$, $\theta^{E,i}_U : M_i(U) \to GE(U)$ and $\theta^{F,i,k}_U : M_i(U) \to F_k(U)$, subject to: $\Gamma(P,U)$-linearity of all three (`hϑs`, `hθEs`, `hθFs`); naturality of all three for the restrictions (`hϑn`, `hθEn`, `hθFn`); exactness, $\operatorname{range} \vartheta^i_U = \ker \theta^{E,i}_U$ (`hexact`); surjectivity of $\theta^{E,i}_U$ (`hsurj`); injectivity of $\vartheta^i_U$ (`hϑi`); and the three compatibilities $(\varphi_k)_U \circ \theta^{F,i,k+1}_U = \theta^{F,i,k}_U$ (`hc1`), $\theta^{F,i,k}_U \circ \vartheta^i_U = (\lambda_k)_U$ (`hc2`) and $(\varepsilon_k)_U \circ \theta^{F,i,k}_U = (\psi^E_k)_U \circ \theta^{E,i}_U$ (`hc3`).
--
--   Finally, the overlap data consists of $A$-linear maps $u_{ij,W} : M_i(W) \to M_j(W)$ for every affine open $W \le K.U_i$ that also satisfies $W \le K.U_j$, which are bijective (`hub`), $\Gamma(P,W)$-linear for the two $\Gamma$-module structures given by `iΓ` (`hus`), natural for restrictions (`hun`), compatible with the $\vartheta$'s, $u_{ij,W} \circ \vartheta^i_W = \vartheta^j_W$ (`huϑ`), compatible with the $\theta^E$'s, $\theta^{E,j}_W \circ u_{ij,W} = \theta^{E,i}_W$ (`huθE`), and satisfying the cocycle identity $u_{jl,W} \circ u_{ij,W} = u_{il,W}$ (`hcocy`).
--
--   The conclusion asserts the existence of a new family of $A$-linear maps $\theta''^{\,i,k}_U : M_i(U) \to F_k(U)$ such that: (i) each $\theta''^{\,i,k}_U$ is $\Gamma(P,U)$-linear; (ii) each is natural for the restrictions, $\theta''^{\,i,k}_{U'} \circ \operatorname{res}_i^h = (F_k).\mathrm{res}\, h \circ \theta''^{\,i,k}_U$; (iii) $(\varphi_k)_U \circ \theta''^{\,i,k+1}_U = \theta''^{\,i,k}_U$; (iv) $\theta''^{\,i,k}_U \circ \vartheta^i_U = (\lambda_k)_U$; (v) $(\varepsilon_k)_U \circ \theta''^{\,i,k}_U = (\psi^E_k)_U \circ \theta^{E,i}_U$; and, conjoined to these, the existence of a new family of $A$-linear overlap maps $u''_{ij,W} : M_i(W) \to M_j(W)$ such that: (vi) each $u''_{ij,W}$ is bijective; (vii) each is $\Gamma(P,W)$-linear; (viii) each is natural for restrictions; (ix) $u''_{ij,W} \circ \vartheta^i_W = \vartheta^j_W$; (x) $\theta^{E,j}_W \circ u''_{ij,W} = \theta^{E,i}_W$; (xi) the cocycle identity $u''_{jl,W} \circ u''_{ij,W} = u''_{il,W}$ holds; and (xii) the new comparison maps are compatible with the new gluing, $\theta''^{\,j,k}_W \circ u''_{ij,W} = \theta''^{\,i,k}_W$ for all $i, j$, all $k$, and all affine $W$ contained in both $K.U_i$ and $K.U_j$.
--
--   Thus the given $\theta^{F}$ and $u$ occur only among the hypotheses: no relation between $u''$ and $u$, or between $\theta''$ and $\theta^F$, is asserted beyond the fact that $u''$ and $\theta''$ satisfy the same list of conditions as $u$ and $\theta^F$, with the extra compatibility (xii).
--
--   This is the twisting step of a formal descent argument in the style of the theory of formal functions for proper morphisms over a complete Noetherian base (EGA III, §4–5): the chart-wise comparison maps to the system $(F_k)$ are modified by a Čech $1$-cochain of the internal Hom of $GE$ into $GK$ so that, after correspondingly modifying the overlap isomorphisms, the comparison maps glue. It feeds into [`AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_isProper_of_isAdicComplete`](thm.html#AlgebraicGeometry.OModulePresheaf.exists_basisData_of_chartData_of_isProper_of_isAdicComplete), and it is obtained from `exists_cocycle_comp_eq_of_chartData_of_internalHom_cocycle` together with the internal-Hom coherence statement `isCoherent_internalHom_and_existsUnique_eval_eq`, the cochain construction `exists_internalHom_cochain_lam_comp_eval_comp_eq_sub_of_chartData_of_cocycle`, and the adic approximation of cocycles `exists_d_eq_zero_forall_sub_sub_d_mem_pow_smul_of_isAdicComplete_of_isProper`.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AlgebraicGeometry_OModulePresheaf_exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete.lean

import Mathlib
import Definitions.Def_AlgebraicGeometry_OModulePresheafHom

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

theorem AlgebraicGeometry.OModulePresheaf.exists_cocycle_comp_eq_of_chartData_of_isProper_of_isAdicComplete
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
    :
    ∃ (θF'' : ∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), M i U →ₗ[A] (F k).obj U.1.1),
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}) (a : Γ(P, U.1.1)) (x : M i U),
        θF'' i k U (a • x) = a • θF'' i k U x) ∧
      (∀ (i : K.ι) (k : ℕ) (U U' : {U : P.affineOpens // U.1 ≤ K.U i}) (h : U'.1.1 ≤ U.1.1) (x : M i U),
        θF'' i k U' (res i h x) = (F k).res h (θF'' i k U x)) ∧
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (φ k).app U.1 ∘ₗ θF'' i (k + 1) U = θF'' i k U) ∧
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), θF'' i k U ∘ₗ ϑ i U = (lam k).app U.1) ∧
      (∀ (i : K.ι) (k : ℕ) (U : {U : P.affineOpens // U.1 ≤ K.U i}), (ε k).app U.1 ∘ₗ θF'' i k U = (ψE k).app U.1 ∘ₗ θE i U) ∧
    ∃ (u'' : ∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), M i W →ₗ[A] M j ⟨W.1, hj⟩),
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j), Function.Bijective (u'' i j W hj)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (a : Γ(P, W.1.1)) (x : M i W),
        letI : Module Γ(P, W.1.1) (M j ⟨W.1, hj⟩) := iΓ j ⟨W.1, hj⟩
        u'' i j W hj (a • x) = a • u'' i j W hj x) ∧
      (∀ (i j : K.ι) (W W' : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (h : W'.1.1 ≤ W.1.1) (x : M i W),
        u'' i j W' (h.trans hj) (res i h x) = res j (U := ⟨W.1, hj⟩) (U' := ⟨W'.1, h.trans hj⟩) h (u'' i j W hj x)) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : GK.obj W.1.1), u'' i j W hj (ϑ i W x) = ϑ j ⟨W.1, hj⟩ x) ∧
      (∀ (i j : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W), θE j ⟨W.1, hj⟩ (u'' i j W hj x) = θE i W x) ∧

      (∀ (i j l : K.ι) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (hl : W.1.1 ≤ K.U l) (x : M i W),
        u'' j l ⟨W.1, hj⟩ hl (u'' i j W hj x) = u'' i l W hl x) ∧
      (∀ (i j : K.ι) (k : ℕ) (W : {U : P.affineOpens // U.1 ≤ K.U i}) (hj : W.1.1 ≤ K.U j) (x : M i W),
        θF'' j k ⟨W.1, hj⟩ (u'' i j W hj x) = θF'' i k W x) := by sorry
