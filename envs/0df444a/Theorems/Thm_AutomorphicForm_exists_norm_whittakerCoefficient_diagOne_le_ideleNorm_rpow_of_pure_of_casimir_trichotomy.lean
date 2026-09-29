-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
-- name    : AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/49b7672f-1111-538d-904c-f2b95eb6e464
-- title:
--   Coordinatewise torus decay of Whittaker coefficients under a Casimir trichotomy
-- statement:
--   Let $K$ be a number field in which any two complex places coincide (so $K$ has at most one complex place), let $D$ be a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, and take the carrier data `productionPinsOf K D` with level subgroups $N\mapsto$ `levelOne` $\sqcap$ $\ker(\mathrm{glArch})$, Hecke generators `heckeGen`, and the adelic box; its central subgroup is all of $(\mathbb{A}_K)^\times$, its measure on $\mathbb{A}_K$ is additive Haar measure conditioned on the box, and its measure on $\mathrm{GL}_2(\mathbb{A}_K)$ is Haar measure for the Borel structure. Let $\xi$ be a character of that central subgroup with $\|\xi(z)\|=\|z\|_{\mathbb{A}}^{w_0}$, where $\|\cdot\|_{\mathbb{A}}$ is the idele norm given by the `distribHaarChar` scaling factor. Let $x:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, invariant under left multiplication by the image of $\mathrm{GL}_2(K)$, and satisfy $x(z\,g)=\xi(z)x(g)$ for central scalars $z$. Write $W(\varphi)(g)=\int \varphi(n(u)g)\,\psi(-u)\,d\nu(u)$ for the Whittaker coefficient at $\alpha=1$ attached to the standard additive character $\psi$, $n(u)$ the upper unipotent. Assume integers $n_v$ and reals $\lambda_v$ indexed by the real places $v$ such that: $x$ has pure weight $n_v$ at $v$ in the sense of `HasArchCharacterAt₀` for `archWeightCharAt hv (nw v hv)`; every iterated flow derivative of $x$ along words in the directions $H,E,F$ at $v$ is smooth in the sense of `IsArchSmoothAt` and continuous; $\|W(x)(g)\|\le C_0\|\det g\|_{\mathbb{A}}^{w_0/2}$ for some $C_0$; $\Omega_v x=\lambda_v x$ for the Casimir operator $-\bigl(\tfrac14 D_H^2-\tfrac12 D_H+D_ED_F\bigr)$ at $v$; and at each real place one of three alternatives holds: (A) $\lambda_v>0$; (B) there are $\varepsilon=\pm1$, $k_0\ge 2$ and $M\in\mathbb{N}$ with $\lambda_v=\tfrac{k_0}{2}\bigl(1-\tfrac{k_0}{2}\bigr)$, $n_v=\varepsilon(k_0+2M)$, $L^{M+1}x=0$ for $L=D_H-\varepsilon i(D_E+D_F)$, and $\|W(L^{M}x)(g)\|\le M'\|\det g\|_{\mathbb{A}}^{w_0/2}$ for some $M'$; (C) $\lambda_v=0$ and $x(g\,h)=x(g)$ for every $h$ in the image of $\mathrm{SL}_2(\mathbb{R})$ at $v$. Assume further, at each complex place $v$, that for every idele $b$ with trivial finite component there are $\delta>0$ and $C$ with $\|W(x)(\mathrm{diag}(a,1))\|\le C\,\|a_v\|^{m_v w_0/2}\min(1,\|a_v\|)^{\delta}$ for all ideles $a$ with trivial finite component whose infinite components agree with those of $b$ away from $v$, where $m_v$ is the multiplicity of $v$. Then there exist $\delta>0$ and $C$ such that for every idele $a$ with trivial finite component, $$\|W(x)(\mathrm{diag}(a,1))\|\le C\prod_{w\mid\infty}\Bigl(\|a_w\|^{m_w w_0/2}\min(1,\|a_w\|)^{\delta}\Bigr).$$
--
--   This is the archimedean decay estimate for Whittaker functions of automorphic forms on $\mathrm{GL}_2$, in per-place (product) form: the three alternatives at a real place correspond to Bargmann's classification of the local archimedean component (principal or complementary series, discrete series with its lowering tower, trivial), and the hypotheses are conditions on a single function, hence apply to finite-adelic translates of a pure-weight form. It is used by the two statements for cuspidal constituents that produce the corresponding bound for forms with trivial archimedean component, in the totally real case and in the case of one complex place.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy.lean

import Definitions.Def_AutomorphicForm_ProductionPinsGeneral
import Definitions.Def_AutomorphicForm_ArchDerivCasimir
import Definitions.Def_AutomorphicForm_ArchWeightCharTransport
import Definitions.Def_AutomorphicForm_WhittakerCoefficient
import Definitions.Def_NumberField_AdelicTraceFin
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicBox
open AutomorphicForm AutomorphicForm.WindowedSiegel AutomorphicForm.SiegelCovering IsDedekindDomain

theorem AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy
    (K : Type) [Field K] [NumberField K]
    (h1 : ∀ v v' : InfinitePlace K, v.IsComplex → v'.IsComplex → v = v')
    (D : Set (AdelicGL2 (𝓞 K) K))
    (ξ : (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)).Z →* ℂˣ)
    (w₀ : ℝ)
    (hξ : ∀ z : (AdeleRing (𝓞 K) K)ˣ,
      ‖((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ)‖ = NumberField.TateGlobal.ideleNorm K z ^ w₀)
    (x : AdelicGL2 (𝓞 K) K → ℂ) (hxc : Continuous x)
    (hxG : ∀ (γ : GL (Fin 2) K) (g : AdelicGL2 (𝓞 K) K), x (globalPoints (𝓞 K) K γ * g) = x g)
    (hxZ : ∀ (z : (AdeleRing (𝓞 K) K)ˣ) (g : AdelicGL2 (𝓞 K) K),
      x (centralScalar (𝓞 K) K z * g) = ((ξ ⟨z, Subgroup.mem_top z⟩ : ℂˣ) : ℂ) * x g)
    (nw : ∀ v : InfinitePlace K, v.IsReal → ℤ) (lam : ∀ v : InfinitePlace K, v.IsReal → ℝ)
    (hxn : ∀ (v : InfinitePlace K) (hv : v.IsReal), HasArchCharacterAt₀ K v (archWeightCharAt hv (nw v hv)) x)
    (hreg : ∀ (v : InfinitePlace K) (hv : v.IsReal) (l : List ArchDir),
      IsArchSmoothAt hv (l.foldr (archDerivAt hv) x) ∧ Continuous (l.foldr (archDerivAt hv) x))
    (hgr : ∃ C₀ : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
      ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              g‖ ≤
        C₀ * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2))
    (hcas : ∀ (v : InfinitePlace K) (hv : v.IsReal), archCasimirAt hv x = ((lam v hv : ℝ) : ℂ) • x)
    (harch : ∀ (v : InfinitePlace K) (hv : v.IsReal),
      0 < lam v hv ∨
      (∃ (ε : ℝ) (k₀ M : ℕ), (ε = 1 ∨ ε = -1) ∧ 2 ≤ k₀ ∧ lam v hv = ((k₀ : ℝ) / 2) * (1 - (k₀ : ℝ) / 2) ∧
        ((nw v hv : ℤ) : ℝ) = ε * (k₀ + 2 * M) ∧ (fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M + 1] x = 0 ∧
        ∃ Mgr : ℝ, ∀ g : AdelicGL2 (𝓞 K) K,
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) ((fun z : AdelicGL2 (𝓞 K) K → ℂ =>
          archDerivAt hv .H z - ((ε : ℂ) * Complex.I) • (archDerivAt hv .E z + archDerivAt hv .Fm z))^[M] x) 1
              g‖ ≤
            Mgr * NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ^ (w₀ / 2)) ∨
      (lam v hv = 0 ∧ ∀ (g : AdelicGL2 (𝓞 K) K) (h : GL (Fin 2) ℝ),
        Matrix.GeneralLinearGroup.det h = 1 → x (g * archRealGLAt hv h) = x g))
    (hcx : ∀ (v : InfinitePlace K), v.IsComplex → ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 →
      ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ v → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a)‖ ≤
            C * ‖((a : AdeleRing (𝓞 K) K)).1 v‖ ^ ((v.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 v‖) ^ δ) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a)‖ ≤
          C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by sorry
