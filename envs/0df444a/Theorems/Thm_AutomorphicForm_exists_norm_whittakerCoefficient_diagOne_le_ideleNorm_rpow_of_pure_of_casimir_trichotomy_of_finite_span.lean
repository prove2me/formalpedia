-- Prove2me | Theorems.Thm_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy_of_finite_span
-- name    : AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy_of_finite_span
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/f7bd33a2-0f23-5081-93cb-3bc805fcbc0d
-- title:
--   Coordinatewise torus decay of Whittaker coefficients under Casimir trichotomy
-- statement:
--   Let $K$ be a number field, $D$ a subset of $\mathrm{GL}_2(\mathbb{A}_K)$, and let the carrier data be `productionPinsOf K D` with level subgroups $N \mapsto \mathrm{levelOne}(N)\cap\ker(\mathrm{glArch})$, Hecke generators $\mathrm{diag}(\pi_v,1)$ at the finite places, and window $\mathrm{adelicBox}\,K$; the associated measure on $\mathbb{A}_K$ is additive Haar measure conditioned on that box, and $W(\phi)(g)=\int \phi(n(u)g)\,\psi(-u)\,du$ denotes `whittakerCoefficient` at $\alpha=1$ for $\psi$ the standard additive character. Since the central subgroup of the data is all of $\mathbb{A}_K^\times$, $\xi$ is a character of $\mathbb{A}_K^\times$ into $\mathbb{C}^\times$, assumed to satisfy $|\xi(z)|=\|z\|^{w_0}$ for a real $w_0$, with $\|\cdot\|$ the idele norm given by the module of the translation action. Let $x:\mathrm{GL}_2(\mathbb{A}_K)\to\mathbb{C}$ be continuous, invariant under left translation by $\mathrm{GL}_2(K)$, and transforming by $\xi$ under the central scalars. Given integers $n_v$ and reals $\lambda_v$ indexed by the real places, assume: at each real place $v$, $x$ satisfies `HasArchCharacterAt₀` for the $n_v$-th power of the weight-one character `archWeightOneAt`; every iterated flow derivative of $x$ in the directions $H,E,F$ at $v$ is `IsArchSmoothAt` and continuous; $W(x)(g)$ is bounded by $C_0\|\det g\|^{w_0/2}$ uniformly in $g$; the Casimir operator `archCasimirAt` at $v$ acts on $x$ by $\lambda_v$; and one of three alternatives holds at $v$ — either $\lambda_v>0$, or there exist $\varepsilon=\pm 1$, $k_0\ge 2$ and $M\in\mathbb{N}$ with $\lambda_v=\tfrac{k_0}{2}(1-\tfrac{k_0}{2})$, $n_v=\varepsilon(k_0+2M)$, $(D_H-\varepsilon i (D_E+D_F))^{M+1}x=0$ and $W$ of $(D_H-\varepsilon i (D_E+D_F))^{M}x$ bounded by a multiple of $\|\det g\|^{w_0/2}$, or $\lambda_v=0$ and $x$ is invariant under right translation by the determinant-one part of $\mathrm{GL}_2(\mathbb{R})$ at $v$. At each complex place $v$ assume two things for ideles with trivial finite component: a one-variable bound, namely for each such $b$ there are $\delta>0$ and $C$ with $\|W(x)(\mathrm{diag}(a,1))\|\le C\,\|a_v\|^{m_v w_0/2}(\min(1,\|a_v\|))^{\delta}$ for all such $a$ agreeing with $b$ away from $v$; and a finite-rank property, namely finitely many functions $\varphi_1,\dots,\varphi_d$ on $K_v$ such that for each such $b$ the function $a\mapsto W(x)(\mathrm{diag}(a,1))$, on the ideles agreeing with $b$ away from $v$, is a $\mathbb{C}$-linear combination of the $\varphi_k(a_v)$. The conclusion is the existence of $\delta>0$ and $C$ with $$\|W(x)(\mathrm{diag}(a,1))\|\le C\prod_{w\ \text{infinite}}\|a_w\|^{m_w w_0/2}\bigl(\min(1,\|a_w\|)\bigr)^{\delta}$$ for every idele $a$ with trivial finite component, $m_w$ being the local multiplicity of $w$.
--
--   This is the archimedean core of the rapid-decay estimate for Whittaker functions on $\mathrm{GL}_2$ over an arbitrary number field: the Bargmann trichotomy (principal/complementary series, discrete series of weight $k_0$ with lowering exponent $M$, and the trivial-Casimir invariant case) at the real places is combined with a one-place bound and a finite-rank condition at the complex places to yield a bound that is a product over all infinite places. It feeds the decay estimate for Whittaker coefficients of cuspidal constituents with at least two complex places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy_of_finite_span.lean

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

theorem AutomorphicForm.exists_norm_whittakerCoefficient_diagOne_le_ideleNorm_rpow_of_pure_of_casimir_trichotomy_of_finite_span
    (K : Type) [Field K] [NumberField K]
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
            C * ‖((a : AdeleRing (𝓞 K) K)).1 v‖ ^ ((v.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 v‖) ^ δ)
    (hcu : ∀ (v : InfinitePlace K), v.IsComplex → ∃ (d : ℕ) (φ : Fin d → v.Completion → ℂ),
      ∀ b : (AdeleRing (𝓞 K) K)ˣ, ((b : AdeleRing (𝓞 K) K)).2 = 1 → ∃ cb : Fin d → ℂ,
        ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
          (∀ w' : InfinitePlace K, w' ≠ v → ((a : AdeleRing (𝓞 K) K)).1 w' = ((b : AdeleRing (𝓞 K) K)).1 w') →
          whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a) = ∑ k, cb k * φ k (((a : AdeleRing (𝓞 K) K)).1 v)) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ C : ℝ,
      ∀ a : (AdeleRing (𝓞 K) K)ˣ, ((a : AdeleRing (𝓞 K) K)).2 = 1 →
        ‖whittakerCoefficient K (productionPinsOf K D
        (fun N => levelOne (𝓞 K) K N ⊓ finiteAdelicGL2Subgroup K) (fun v => heckeGen (𝓞 K) K v) (adelicBox K)) (NumberField.StandardAddChar.stdAddChar K) x 1
              (diagOne a)‖ ≤
          C * ∏ w : InfinitePlace K, (‖((a : AdeleRing (𝓞 K) K)).1 w‖ ^ ((w.mult : ℝ) * w₀ / 2) * (min 1 ‖((a : AdeleRing (𝓞 K) K)).1 w‖) ^ δ) := by sorry
