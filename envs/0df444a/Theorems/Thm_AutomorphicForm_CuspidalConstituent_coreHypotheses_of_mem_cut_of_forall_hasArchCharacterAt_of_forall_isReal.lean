-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal
-- name    : AutomorphicForm.CuspidalConstituent.coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/e1d657fc-42f6-5041-87d8-9ea841128239
-- title:
--   Core archimedean hypotheses for pure-weight cut vectors, totally real case
-- statement:
--   Let $K$ be a number field, $c,u,d_1,d_2$ real with $c>0$ and $0<d_1<d_2$, and $T$ a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Put $D=\bigcup_{x\in T}\,(\,\cdot\,x)(\,\mathrm{centreCutSiegelSet}\;K\,c\,u\,d_1\,d_2)$, the union of the right translates by elements of $T$ of the set of $g$ whose finite part is integral, whose archimedean components all have local height $\ge c$, window $\mathrm{xWindowSq}\le u^2$ and archimedean determinant norm in $[d_1,d_2]$, and assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left multiplication by $\mathrm{GL}_2(K)$ and right multiplication by central ideles. Carrier data are those of `productionPinsOf` for $D$, the level subgroups $N\mapsto \mathrm{levelOne}\,N\cap\ker(\mathrm{glArch})$, the Hecke generators $\mathrm{heckeGen}\,v$, and the box $\mathrm{adelicBox}\,K$ (central subgroup $Z=\top$, Haar measures, and the adelic additive Haar measure conditioned to the box). Let $\xi$ be a character of the full idele class group $Z$ with values in $\mathbb{C}^\times$, and $V$ a $\mathbb{C}$-subspace of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ that is a cuspidal constituent: $V$ lies in the $K$-finite cusp space for $\xi$, is stable under right translation by finite-adelic elements, by the subgroups $\mathrm{rowIsometrySubgroup}_0$ at each infinite place and by right convolution with factorizable archimedean-bi-finite test functions, is non-zero, and has no proper non-zero such subspace. Assume every infinite place of $K$ is real. Let $N\ne 0$ be an ideal, $\mathrm{tys}$ a family of archimedean types, and $y$ an element of $V$ that is right invariant under $\mathrm{levelOne}\,N\cap\ker(\mathrm{glArch})$ and lies in the archimedean cut space $\mathrm{archCutSubmodule}\,\mathrm{tys}$. Let $w_0\in\mathbb{R}$ with $\|\xi(z)\|=\mathrm{ideleNorm}(z)^{w_0}$ for all ideles $z$, let $n_v\in\mathbb{Z}$ be given for each real place $v$, and assume $y$ satisfies `HasArchCharacterAt₀` at each real place $v$ for the character $\mathrm{archWeightCharAt}$ of exponent $n_v$, the $n_v$-th power of the weight-one archimedean character at $v$. Then: $y$ is continuous; $y(\gamma g)=y(g)$ for $\gamma\in\mathrm{GL}_2(K)$ embedded adelically; $y(zg)=\xi(z)y(g)$ for central ideles $z$; for every real place $v$ and every finite word $l$ in the directions $H,E,F^-$ the iterated flow derivative $\mathrm{archDerivAt}$ applied along $l$ to $y$ is archimedean-smooth at $v$ and continuous; there is $C_0$ with $\|W(y)(g)\|\le C_0\,\|\det g\|^{w_0/2}$, where $W$ is the first Whittaker coefficient for the standard additive character; and there are real numbers $\lambda_v$ with $\mathrm{archCasimirAt}_v\,y=\lambda_v\,y$ such that for each real place $v$ either $\lambda_v>0$, or there are $\varepsilon=\pm1$, $k_0\ge 2$ and $M\in\mathbb{N}$ with $\lambda_v=\tfrac{k_0}{2}\bigl(1-\tfrac{k_0}{2}\bigr)$, $n_v=\varepsilon(k_0+2M)$, $\mathcal{L}_\varepsilon^{M+1}y=0$ for $\mathcal{L}_\varepsilon=D_H-\varepsilon i\,(D_E+D_{F^-})$, and a bound $\|W(\mathcal{L}_\varepsilon^{M}y)(g)\|\le M'\|\det g\|^{w_0/2}$, or $\lambda_v=0$ and $y$ is invariant under right translation by the elements of $\mathrm{GL}_2(\mathbb{R})$ of determinant $1$ included at $v$.
--
--   The conclusion is precisely the hypothesis package of the level-free archimedean analysis of such vectors: continuity, left $\mathrm{GL}_2(K)$-invariance, central character, smoothness and continuity of all words of flow derivatives, polynomial growth of the first Whittaker coefficient, real Casimir eigenvalues, and Bargmann's trichotomy at each real place (principal or complementary series; discrete series of weight $k_0$ together with vanishing of the $(M+1)$-st iterate of the lowering or raising operator and growth of the $M$-th iterate; or the trivial case). It is used in the derivation of Whittaker-coefficient bounds for finite translates of cut vectors of a cuspidal constituent over a totally real field.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_CuspidalConstituent
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain
open AutomorphicForm.CuspidalConstituent

theorem AutomorphicForm.CuspidalConstituent.coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt_of_forall_isReal
    (K : Type) [Field K] [NumberField K]
    (c u d₁ d₂ : ℝ) (T : Finset (AdelicGL2 (𝓞 K) K))
    (hc : 0 < c) (hd₁ : 0 < d₁) (hd : d₁ < d₂)
    (hcov : CoversModCentre K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂))
    (ξ : (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)).Z →* ℂˣ)
    (V : Submodule ℂ (AdelicGL2 (𝓞 K) K → ℂ))
    (hV : IsCuspConstituent K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) ξ V)
    (hreal : ∀ v : InfinitePlace K, v.IsReal)
    (N : Ideal (𝓞 K)) (hN : N ≠ ⊥) (tys : AutomorphicForm.ArchTypeFamily K)
    (y : AdelicGL2 (𝓞 K) K → ℂ)
    (hy : y ∈ V ⊓ levelInvariantSubmodule K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) N ⊓ archCutSubmodule K tys)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (nw : ∀ v : InfinitePlace K, v.IsReal → ℤ)
    (hyn : ∀ (v : InfinitePlace K) (hv : v.IsReal), HasArchCharacterAt₀ K v (archWeightCharAt hv (nw v hv)) y) :
    Continuous y ∧
    (∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), y (globalPoints (𝓞 K) K γ * g) = y g) ∧
    (∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      y (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * y g) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsReal) (l : List ArchDir),
      IsArchSmoothAt hv (l.foldr (archDerivAt hv) y) ∧ Continuous (l.foldr (archDerivAt hv) y)) ∧
    (∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) y 1
              g‖ ≤
        C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∧
    ∃ lam : ∀ v : InfinitePlace K, v.IsReal → ℝ,
      (∀ (v : InfinitePlace K) (hv : v.IsReal), archCasimirAt hv y = ((lam v hv : ℝ) : ℂ) • y) ∧
      ∀ (v : InfinitePlace K) (hv : v.IsReal),
        0 < lam v hv ∨
        (∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ lam v hv = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
          ((nw v hv : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M + 1] y = 0 ∧
          ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
            ‖whittakerCoefficient K (productionPinsOf K (⋃ x ∈ T, (· * x) '' centreCutSiegelSet K c u d₁ d₂)
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v)
        (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M] y) 1
              g‖ ≤
              Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∨
        (lam v hv = 0 ∧ ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
          Matrix.GeneralLinearGroup.det h = 1 → y (g * archRealGLAt hv h) = y g) := by sorry
