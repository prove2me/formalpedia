-- Prove2me | Theorems.Thm_AutomorphicForm_CuspidalConstituent_coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt
-- name    : AutomorphicForm.CuspidalConstituent.coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:50.966433+00:00
-- url     : https://prove2.me/theorems/dec909c1-60cb-53de-9225-8d4ed9bffc5f
-- title:
--   Real-place archimedean core hypotheses for pure-weight cut vectors
-- statement:
--   Let $K$ be a number field, let $c,u,d_1,d_2$ be reals with $c>0$ and $0<d_1<d_2$, and let $T$ be a finite subset of $\mathrm{GL}_2(\mathbb{A}_K)$. Write $D=\bigcup_{x\in T}\,(\,\cdot\,x)\,[\,\mathrm{centreCutSiegelSet}\,K\,c\,u\,d_1\,d_2\,]$, the union of the right translates by the elements of $T$ of the set of $g$ whose finite part is integral, whose local height at every infinite place is at least $c$, whose $x$-window satisfies $\mathrm{xWindowSq}\le u^2$, and whose archimedean determinant norms all lie in $[d_1,d_2]$; assume $D$ covers $\mathrm{GL}_2(\mathbb{A}_K)$ modulo left $\mathrm{GL}_2(K)$ and right centre, i.e. every $g$ admits $\gamma\in\mathrm{GL}_2(K)$ and $z\in\mathbb{A}_K^\times$ with $\gamma g\,z\in D$. Let the carrier data be `productionPinsOf` for $D$, for the levels $N\mapsto\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, for the Hecke generators $v\mapsto\mathrm{heckeGen}\,v$ and for the adelic box, so that the central subgroup is all of $\mathbb{A}_K^\times$, the measure on $\mathbb{A}_K$ is additive Haar conditioned on the box, and the measure on $\mathrm{GL}_2(\mathbb{A}_K)$ is Haar for the Borel structure. Let $\xi:\mathbb{A}_K^\times\to\mathbb{C}^\times$ be a character and $V$ a $\mathbb{C}$-subspace of functions $\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ which is a cuspidal constituent for these data: $V$ is a cusp $K$-finite subrepresentation (contained in `cuspKFiniteSubmodule`, stable under right translation by the finite adelic subgroup and by the groups $\mathrm{rowIsometrySubgroup}_0$ at the infinite places, and under right convolution by factorizable archimedeanly bi-finite test functions), $V\neq 0$, and every such subrepresentation contained in $V$ is $0$ or $V$. Let $N\neq 0$ be an ideal of $\mathcal{O}_K$, let $\mathrm{tys}$ be an archimedean type family, and let $y$ lie in $V$, be right-invariant under $\mathrm{levelOne}(N)\sqcap\mathrm{finiteAdelicGL2Subgroup}$, and lie in $\mathrm{archCutSubmodule}\,\mathrm{tys}$, the intersection over infinite places of the sums of the type submodules of the family. Assume $\|\xi(z)\|=\mathrm{ideleNorm}(z)^{w_0}$ for all $z$ and some $w_0\in\mathbb{R}$, and that integers $n_v$ are given for the real places $v$ with $y$ satisfying the pure-weight condition `HasArchCharacterAt₀` at $v$ for the character $\mathrm{archWeightCharAt}\,h_v\,(n_v)$, the $n_v$-th power of the weight-one character at $v$. Then: $y$ is continuous; $y(\gamma g)=y(g)$ for $\gamma\in\mathrm{GL}_2(K)$ embedded by `globalPoints`; $y(zg)=\xi(z)y(g)$ for central scalars $z\in\mathbb{A}_K^\times$; for every real place $v$ and every finite word $l$ in the directions $H,E,F^-$, the iterated flow derivative $\mathrm{archDerivAt}$ along $l$ applied to $y$ is archimedeanly smooth at $v$ and continuous; there is $C_0$ with $\|W(y)(g)\|\le C_0\,\mathrm{ideleNorm}(\det g)^{w_0/2}$ for all $g$, where $W$ is the Whittaker coefficient at the parameter $1$ for the standard additive character; and there are reals $\lambda_v$, indexed by the real places, with $\mathrm{archCasimirAt}\,h_v\,y=\lambda_v\cdot y$ and, for each real place $v$, either $\lambda_v>0$, or there exist $\varepsilon=\pm1$, $k_0\ge 2$ and $M\in\mathbb{N}$ with $\lambda_v=\frac{k_0}{2}\bigl(1-\frac{k_0}{2}\bigr)$, $n_v=\varepsilon(k_0+2M)$, $L_\varepsilon^{M+1}y=0$ for $L_\varepsilon=\mathrm{archDerivAt}\,H-\varepsilon i\,(\mathrm{archDerivAt}\,E+\mathrm{archDerivAt}\,F^-)$, and some $M'$ with $\|W(L_\varepsilon^{M}y)(g)\|\le M'\,\mathrm{ideleNorm}(\det g)^{w_0/2}$ for all $g$, or $\lambda_v=0$ and $y(g\,\mathrm{archRealGLAt}\,h_v\,h)=y(g)$ for all $g$ and all $h\in\mathrm{GL}_2(\mathbb{R})$ of determinant $1$. Nothing is assumed or concluded at the complex places.
--
--   This packages, for a vector of pure weight in a cuspidal constituent cut out by a covering union of translates of a centre-cut Siegel set, exactly the real-place input list of the archimedean core used for torus decay of Whittaker functions: continuity, left $\mathrm{GL}_2(K)$-invariance, central character, smoothness and continuity of all words in the flow derivatives, the Whittaker growth bound, and real Casimir eigenvalues subject to Bargmann's trichotomy (positive eigenvalue; discrete-series eigenvalue with one-sided vanishing of the lowering/raising operator; or right $\mathrm{SL}_2(\mathbb{R})$-invariance). It feeds the two subsequent bounds for Whittaker coefficients along the diagonal torus at the infinite places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_CuspidalConstituent_coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt.lean

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

theorem AutomorphicForm.CuspidalConstituent.coreHypotheses_of_mem_cut_of_forall_hasArchCharacterAt
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
