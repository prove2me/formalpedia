-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
-- name    : AutomorphicForm.exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/6b9602a9-544b-5989-b136-d2f045ab1ca1
-- title:
--   Haar normalisation on the centralizer of an adelic scalar in GL₂
-- statement:
--   Let $K$ be a number field, $\mathbb{A}_K$ its adele ring, and let $G=\mathrm{GL}_2(\mathbb{A}_K)$ carry the Borel $\sigma$-algebra of its topology and the Haar measure `adelicGLHaar`; write $\|x\|$ for [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the value at $x$ of the distributive Haar character of $\mathbb{A}_K$, and let $\Gamma$ be the image of $\mathrm{GL}_2(K)$ in $G$ under the entrywise map induced by $K\to\mathbb{A}_K$. Let $C_H\in[0,\infty]$ be neither $0$ nor $\infty$ and assume: for all reals $0<a\le b$ and every set $\Phi\subseteq\{g:\|\det g\|\in[a,b]\}$ which is a fundamental domain for $\Gamma$ with respect to the Haar measure restricted to that band, one has $\mu(\Phi)=C_H\log(b/a)$. Let $u\in\mathbb{A}_K^{\times}$, let $\gamma=u\cdot 1$ be the corresponding scalar matrix, let $Z=\mathrm{Cent}_G(\{\gamma\})$ with its Borel structure, and let $C$ be neither $0$ nor $\infty$. Then there is a measure $\tau$ on $Z$ which is a Haar measure, is right invariant, admits a set $D\subseteq Z$ that is a fundamental domain for the opposite group of $\Gamma\cap Z$ (viewed as a subgroup of $Z$) acting on $Z$ with respect to $\tau$, satisfies $\tau\bigl(D\cap\{t:\|\det t\|\in[a,b]\}\bigr)=C\log(b/a)$ for every such fundamental domain $D$ and all $0<a\le b$, and is such that for every $c_0\in\mathbb{R}_{\ge 0}$, every $f:G\to\mathbb{C}$ and every $I\in\mathbb{C}$, the predicate [`AutomorphicForm.IsOrbitalIntegralOn`](def/AutomorphicForm_TwistedOrbital.html#L248) for the measure $c_0\mu$ on $G$, the element $\gamma$, the measure $\tau$ on $Z$, $f$ and $I$ — that is, the existence of a non-negative measurable compactly supported $w:G\to\mathbb{R}$ with $\int_Z w(tx)\,d\tau(t)=1$ for every $x$ with $f(x^{-1}\gamma x)\neq 0$, and $I=\int_G f(x^{-1}\gamma x)w(x)\,d(c_0\mu)(x)$ — holds if and only if $I=c_0\,(C_H/C)\,f(\gamma)$.
--
--   This is the normalisation statement for Haar measure on the centralizer of a central element of $\mathrm{GL}_2(\mathbb{A}_K)$: the measure on the centralizer may be prescribed so that the band covolume of the rational points, for the right action, is any chosen constant $C$, and then the orbital integral at the scalar takes the single value $c_0(C_H/C)f(\gamma)$. It is used in the evaluation of the central contributions to the trace formula, being cited by the two results computing integrals over a centralizer domain as a multiple of $f$ at a central scalar.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_NumberField_TateGlobalZeta
import Definitions.Def_NumberField_AdelicHaar

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open scoped ENNReal

attribute [local instance] NumberField.AdelicHaar.glBorel AutomorphicForm.centralizerBorel

theorem AutomorphicForm.exists_isHaarMeasure_centralizer_forall_isFundamentalDomain_op_inter_eq_mul_log_and_isOrbitalIntegralOn_centralScalar_iff
    (K : Type) [Field K] [NumberField K]
    (C_H : ℝ≥0∞) (hC0 : C_H ≠ 0) (hCt : C_H ≠ ⊤)
    (hC_H : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K),
      Φ ⊆ {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b} →
      IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
        ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
          {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc a b}) →
      adelicGLHaar (Fin 2) (𝓞 K) K Φ = C_H * ENNReal.ofReal (Real.log (b / a)))
    (u : (AdeleRing (𝓞 K) K)ˣ) (C : ℝ≥0∞) (hC0' : C ≠ 0) (hCt' : C ≠ ⊤) :
    ∃ τ : Measure (Subgroup.centralizer
        ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
      τ.IsHaarMeasure ∧ τ.IsMulRightInvariant ∧
      (∃ D : Set (Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        IsFundamentalDomain
          (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
            (Subgroup.centralizer
              ({AutomorphicForm.centralScalar (𝓞 K) K u} :
                Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ) ∧
      (∀ D : Set (Subgroup.centralizer
          ({AutomorphicForm.centralScalar (𝓞 K) K u} : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))),
        IsFundamentalDomain
          (((AutomorphicForm.globalPoints (𝓞 K) K).range).subgroupOf
            (Subgroup.centralizer
              ({AutomorphicForm.centralScalar (𝓞 K) K u} :
                Set (AutomorphicForm.AdelicGL2 (𝓞 K) K)))).op D τ →
        ∀ a b : ℝ, 0 < a → a ≤ b →
          τ (D ∩ {t | NumberField.TateGlobal.ideleNorm K
            (Matrix.GeneralLinearGroup.det (t : AutomorphicForm.AdelicGL2 (𝓞 K) K)) ∈ Set.Icc a b}) =
            C * ENNReal.ofReal (Real.log (b / a))) ∧
      ∀ (c₀ : NNReal) (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (I : ℂ),
        AutomorphicForm.IsOrbitalIntegralOn (AdeleRing (𝓞 K) K) (c₀ • adelicGLHaar (Fin 2) (𝓞 K) K)
            (AutomorphicForm.centralScalar (𝓞 K) K u) τ f I ↔
          I = (((c₀ : ℝ) * (C_H / C).toReal : ℝ) : ℂ) * f (AutomorphicForm.centralScalar (𝓞 K) K u) := by sorry
