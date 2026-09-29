-- Prove2me | Theorems.Thm_AxisWitness_exists_axisContinuation
-- name    : AxisWitness.exists_axisContinuation
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:57.856077+00:00
-- url     : https://prove2.me/theorems/e5f460f6-21cb-507f-aa2e-b276bcf5b945
-- title:
--   Analytic continuation of an adelic GL₂ Eisenstein family
-- statement:
--   Let $L$ be a number field, $\mathbb{A}=\mathbb{A}_L$ its adele ring. Let $\alpha_n:\mathbb{A}^\times\to\mathbb{R}^\times$ be a monoid homomorphism with everywhere positive values which is assumed to be the homomorphism to units induced by the module (distributive Haar) character of $\mathbb{A}$ composed with $\mathbb{R}_{\ge0}\to\mathbb{R}$. Let $\mu,\nu:\mathbb{A}^\times\to\mathbb{C}^\times$ be continuous characters with $|\mu(x)|=|\nu(x)|=1$ for all $x$ and $\mu,\nu$ trivial on the image of $L^\times$. Let $E_f:\mathbb{C}\to\mathrm{GL}_2(\mathbb{A})\to\mathbb{C}$ satisfy: for each $s$, $E_f(s)(bg)=\eta_1(b_{00})\eta_2(b_{11})E_f(s)(g)$ for all $g$ and all $b$ with $b_{10}=0$, where $\eta_1=\mu\cdot\alpha_n^{s+1/2}$, $\eta_2=\nu\cdot\alpha_n^{-(s+1/2)}$; each $E_f(s)$ has finite-dimensional span of right translates under the image of each archimedean row-isometry subgroup, and has open stabiliser under right translation by the kernel of the archimedean projection; $(s,g)\mapsto E_f(s)(g)$ is continuous; $s\mapsto E_f(s)(g)$ is entire for each $g$; and for each infinite place $w$ there is a finite-dimensional space $W$ of functions on the row-isometry subgroup at $w$ containing $k\mapsto E_f(s)(gk)$ for all $s,g$. Then there are an open preconnected $O\subseteq\mathbb{C}$ containing $\{\Re s=0\}$ and $\{\Re s>1/2\}$ and families $E_c,N_c$ such that: $s\mapsto E_c(s)(g)$ and $s\mapsto N_c(s)(g)$ are analytic on a neighbourhood of each point of $O$ for every $g$; both are jointly continuous on $O\times\mathrm{GL}_2(\mathbb{A})$; for $\Re s>1/2$, $E_c(s)(g)=E_f(s)(g)+\sum_{\beta\in L}E_f(s)(w\,u(\beta)g)$ with $w$ the adelic Weyl element and $u(x)=\begin{pmatrix}1&x\\0&1\end{pmatrix}$, and $N_c(s)(g)=\mathrm{vol}(\text{box})^{-1}\int_{\mathbb{A}}E_f(s)(w^{-1}u(x)g)\,dx$, the volume being that of the adelic box for the adelic Haar measure; for every $s\in\mathbb{C}$, $N_c(s)$ is an induced section for the swapped pair at $-s$, i.e. for $(\nu\cdot\alpha_n^{-s+1/2},\mu\cdot\alpha_n^{s-1/2})$; for $s\in O$, $E_c(s)$ is left invariant under the image of $\mathrm{GL}_2(L)$ and satisfies $E_c(s)(zg)=\mu(z)\nu(z)E_c(s)(g)$ for central scalars $z\in\mathbb{A}^\times$; for $s\in O$ the constant term $\int E_c(s)(u(x)g)$ against the Haar measure conditioned to the adelic box equals $E_f(s)(g)+N_c(s)(g)$; and any $u_0$ with $E_f(s)(gu_0)=E_f(s)(g)$ for all $s,g$ also fixes $E_c(s)$ and $N_c(s)$ on the right for all $s\in O$.
--
--   This is the analytic continuation, past the convergence half-plane $\Re s>1/2$ to a connected region also containing the unitary axis, of the Eisenstein series attached to a family of induced sections of $\mathrm{GL}_2$ over the adeles of $L$ for a pair of unitary idele class characters, together with its Weyl (Bruhat cell) intertwining integral, the continued constant-term identity, and the invariance properties of the continued family. It is used in the truncation estimate [`AutomorphicForm.exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain`](thm.html#AutomorphicForm.exists_forall_norm_add_tsum_norm_le_mul_adelicHeight_rpow_of_isInducedSection_of_mem_canonicalTruncationDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AxisWitness_exists_axisContinuation.lean

import Definitions.Def_AutomorphicForm_EtaFamily
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_AutomorphicForm_InducedSection
import Definitions.Def_AutomorphicForm_ArchKFinite
import Definitions.Def_AutomorphicForm_SmoothAutomorphicFnAt
import Definitions.Def_AutomorphicForm_SlabProfile
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_AdelicBox
import Definitions.Def_AutomorphicForm_WeylIntertwining
import Definitions.Def_AutomorphicForm_ConstantTerm

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicLevel NumberField.AdelicHaar NumberField.AdelicBox IsDedekindDomain
open AutomorphicForm
open scoped ComplexConjugate NNReal ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel
attribute [local instance] NumberField.AdelicHaar.adeleBorel

theorem AxisWitness.exists_axisContinuation (L : Type) [Field L] [NumberField L]
    (αn : (AdeleRing (𝓞 L) L)ˣ →* ℝˣ) (hαn : ∀ x, 0 < ((αn x : ℝˣ) : ℝ))
    (hαeq : αn = ((NNReal.toRealHom : ℝ≥0 →+* ℝ).toMonoidHom.comp (distribHaarChar (AdeleRing (𝓞 L) L))).toHomUnits)
    (μ ν : (AdeleRing (𝓞 L) L)ˣ →* ℂˣ) (hμ : IsUnitaryChar (𝓞 L) L μ) (hν : IsUnitaryChar (𝓞 L) L ν)
    (hμc : IsIdeleClassChar (𝓞 L) L μ) (hνc : IsIdeleClassChar (𝓞 L) L ν)
    (hμk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((μ x : ℂˣ) : ℂ))
    (hνk : Continuous fun x : (AdeleRing (𝓞 L) L)ˣ => ((ν x : ℂˣ) : ℂ))
    (Ef : ℂ → AdelicGL2 (𝓞 L) L → ℂ)
    (hEf : ∀ s, IsInducedSection (𝓞 L) L (etaFst μ αn hαn s) (etaSnd ν αn hαn s) (Ef s))
    (hK : ∀ s, IsArchKFinite L (Ef s)) (hf : ∀ s, IsKfSmooth L (Ef s))
    (hjc : Continuous fun p : ℂ × AdelicGL2 (𝓞 L) L => Ef p.1 p.2)
    (hhol : ∀ g : AdelicGL2 (𝓞 L) L, Differentiable ℂ (fun s => Ef s g))
    (hKu : ∀ w : InfinitePlace L, ∃ W : Submodule ℂ (↥(archRowIsometrySubgroup L w) → ℂ),
      FiniteDimensional ℂ W ∧ ∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L),
        (fun k : ↥(archRowIsometrySubgroup L w) => Ef s (g * (k : AdelicGL2 (𝓞 L) L))) ∈ W) :
    ∃ (O : Set ℂ) (Ec Nc : ℂ → AdelicGL2 (𝓞 L) L → ℂ),
      IsOpen O ∧ IsPreconnected O ∧ {s : ℂ | s.re = 0} ⊆ O ∧ {s : ℂ | 1 / 2 < s.re} ⊆ O ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Ec s g) O) ∧
      (∀ g : AdelicGL2 (𝓞 L) L, AnalyticOnNhd ℂ (fun s => Nc s g) O) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Ec p.1 p.2) (O ×ˢ Set.univ) ∧
      ContinuousOn (fun p : ℂ × AdelicGL2 (𝓞 L) L => Nc p.1 p.2) (O ×ˢ Set.univ) ∧
      (∀ s : ℂ, 1 / 2 < s.re → Ec s = pseudoEisenstein L (Ef s)) ∧
      (∀ s : ℂ, 1 / 2 < s.re → ∀ g : AdelicGL2 (𝓞 L) L,
        Nc s g = (((adelicAddHaar (𝓞 L) L) (adelicBox L)).toReal : ℂ)⁻¹ *
          weylIntertwiningIntegral (𝓞 L) L (adelicAddHaar (𝓞 L) L) (Ef s) g) ∧
      (∀ s : ℂ, IsInducedSection (𝓞 L) L (etaFst ν αn hαn (-s)) (etaSnd μ αn hαn (-s)) (Nc s)) ∧
      (∀ s ∈ O, ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (g : AdelicGL2 (𝓞 L) L),
        Ec s (globalPoints (𝓞 L) L γ * g) = Ec s g) ∧
      (∀ s ∈ O, ∀ (z : (AdeleRing (𝓞 L) L)ˣ) (g : AdelicGL2 (𝓞 L) L),
        Ec s (centralScalar (𝓞 L) L z * g) = ((μ z : ℂˣ) : ℂ) * ((ν z : ℂˣ) : ℂ) * Ec s g) ∧
      (∀ s ∈ O, ∀ g : AdelicGL2 (𝓞 L) L,
        @constantTerm (AdeleRing (𝓞 L) L) (adeleBorel (𝓞 L) L) (AdelicGL2 (𝓞 L) L) _
          (@ProbabilityTheory.cond _ (adeleBorel (𝓞 L) L) (adelicAddHaar (𝓞 L) L) (adelicBox L))
          unipotentGL2 (Ec s) g = Ef s g + Nc s g) ∧
      (∀ u₀ : AdelicGL2 (𝓞 L) L, (∀ (s : ℂ) (g : AdelicGL2 (𝓞 L) L), Ef s (g * u₀) = Ef s g) →
        ∀ s ∈ O, ∀ g : AdelicGL2 (𝓞 L) L, Ec s (g * u₀) = Ec s g ∧ Nc s (g * u₀) = Nc s g) := by sorry
