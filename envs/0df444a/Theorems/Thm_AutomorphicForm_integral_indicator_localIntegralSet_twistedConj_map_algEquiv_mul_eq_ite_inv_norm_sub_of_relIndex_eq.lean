-- Prove2me | Theorems.Thm_AutomorphicForm_integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq
-- name    : AutomorphicForm.integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/e2f25e90-883a-5a24-9a24-65ab31770641
-- title:
--   Twisted orbital integral of the unit at split diagonal δ
-- statement:
--   Let $K\subseteq L$ be number fields, $v$ a height-one prime of $\mathcal O_K$ and $w$ a height-one prime of $\mathcal O_L$ lying under $v$, with ramification index of $w$ over the prime it lies under equal to $1$; write $F=K_v$, $E=L_w$ and $q=\mathrm{absNorm}(v)$. Let $\theta$ be an $F$-algebra automorphism of $E$ whose order equals $[E:F]$, acting entrywise on matrices. Let $a,b\in F^\times$ with $a\neq b$ and $\|a-b\|=q^{-m}$ for an integer $m$, and let $\alpha,\beta\in E^\times$ satisfy $\prod_{i<[E:F]}\theta^i(\alpha)=a$, $\prod_{i<[E:F]}\theta^i(\beta)=b$. Assume the $\theta$-twisted centraliser $\{t\in GL_2(E): t\,\delta\,\theta(t)^{-1}=\delta\}$ of $\delta=\mathrm{diag}(\alpha,\beta)$ is the image of the centraliser of $\mathrm{diag}(a,b)$ in $GL_2(F)$; and assume that if $\|a\|=\|b\|=1$ then for every $\varpi\in F$ with $\|\varpi\|=q^{-1}$ and every $s\in\mathbb N$ the additive group $\Lambda=\{y\in E:\theta(y)-\beta\alpha^{-1}y\in\mathcal O_E\}\cap\varpi^{-s}\mathcal O_E$ satisfies $[\Lambda:\Lambda\cap\mathcal O_E]=q^{\min(s,m^+)}$, $m^+=\max(m,0)$. Let $\tau'$ be a Haar measure on the twisted centraliser giving mass $1$ to its elements lying in $U=\{g\in GL_2(E): g,g^{-1}\text{ have entries in }\mathcal O_E\}$, and let $s\ge 0$ be Borel measurable of compact support on $GL_2(E)$ with $\int s(tx)\,d\tau'(t)=1$ whenever $x^{-1}\delta\,\theta(x)\in U$. Then, for the Haar measure on $GL_2(E)$ normalised by $\mu(U)=1$, $$\int_{GL_2(E)}\mathbf 1_{U}\bigl(x^{-1}\delta\,\theta(x)\bigr)\,s(x)\,d\mu(x)=\begin{cases}\|a-b\|^{-1},&\|a\|=\|b\|=1,\\0,&\text{otherwise,}\end{cases}$$ as an identity of complex numbers.
--
--   This is the fundamental lemma for the unit element of the Hecke algebra in cyclic base change for $GL(2)$, at the split (hyperbolic) diagonal twisted classes, over a single unramified local layer of arbitrary degree, formulated through a section function $s$ on the twisted torus rather than through a quotient measure. It is used in the comparison of twisted orbital integrals with orbital integrals of the norm, being cited by [`AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one`](thm.html#AutomorphicForm.norm_sub_norm_mul_le_of_isTwistedOrbitalIntegral_indicator_semiLocalIntegralSet_of_ramificationIdx_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq.lean

import Definitions.Def_AutomorphicForm_LocalOrbitalBase
import Definitions.Def_AutomorphicForm_SigmaCentralizer
import Definitions.Def_LanglandsTunnell_CubicInduction_TorusValues
import Definitions.Def_DedekindDomain_Completion_BaseChange

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField IsDedekindDomain
open LanglandsTunnell.CubicInduction (diagUnits2)

theorem AutomorphicForm.integral_indicator_localIntegralSet_twistedConj_map_algEquiv_mul_eq_ite_inv_norm_sub_of_relIndex_eq
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (v : HeightOneSpectrum (𝓞 K)) (w : v.Extension (𝓞 L))
    (hw : Ideal.ramificationIdx' (HeightOneSpectrum.under (𝓞 K) w.1).asIdeal w.1.asIdeal = 1)
    (θ : w.1.adicCompletion L ≃ₐ[v.adicCompletion K] w.1.adicCompletion L)
    (hθ : orderOf θ = Module.finrank (v.adicCompletion K) (w.1.adicCompletion L))
    (a b : (v.adicCompletion K)ˣ) (hab : a ≠ b) (m : ℤ)
    (hm : ‖(a : v.adicCompletion K) - b‖ = (Ideal.absNorm v.asIdeal : ℝ) ^ (-m))
    (α β : (w.1.adicCompletion L)ˣ)
    (hNα : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (α : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) a)
    (hNβ : ∏ i ∈ Finset.range (Module.finrank (v.adicCompletion K) (w.1.adicCompletion L)),
        (θ ^ i) (β : w.1.adicCompletion L) = algebraMap (v.adicCompletion K) (w.1.adicCompletion L) b)
    (hT : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β) =
      (AutomorphicForm.localCentralizer K v (diagUnits2 a b)).map
        (Matrix.GeneralLinearGroup.map (algebraMap (v.adicCompletion K) (w.1.adicCompletion L))))
    (hidx : ‖(a : v.adicCompletion K)‖ = 1 → ‖(b : v.adicCompletion K)‖ = 1 →
      ∀ ϖ : v.adicCompletion K, ‖ϖ‖ = (Ideal.absNorm v.asIdeal : ℝ)⁻¹ → ∀ s : ℕ,
        (w.1.adicCompletionIntegers L).toAddSubgroup.relIndex
            (((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (θ.toAlgHom.toRingHom.toAddMonoidHom -
                  AddMonoidHom.mulLeft ((β * α⁻¹ : (w.1.adicCompletion L)ˣ) : w.1.adicCompletion L))) ⊓
              ((w.1.adicCompletionIntegers L).toAddSubgroup.comap
                (AddMonoidHom.mulLeft
                  (algebraMap (v.adicCompletion K) (w.1.adicCompletion L) (ϖ ^ s))))) =
          Ideal.absNorm v.asIdeal ^ min s m.toNat)
    (τ' : @Measure (AutomorphicForm.sigmaCentralizer
        (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom) (diagUnits2 α β)) (borel _))
    (hτ' : @Measure.IsHaarMeasure _ _ _ (borel _) τ')
    (hτ'1 : τ' {t | (t : GL (Fin 2) (w.1.adicCompletion L)) ∈ AutomorphicForm.localIntegralSet L w.1} = 1)
    (s : GL (Fin 2) (w.1.adicCompletion L) → ℝ) (hs0 : ∀ x, 0 ≤ s x)
    (hsm : Measurable[AutomorphicForm.localGLBorel L w.1] s) (hsc : HasCompactSupport s)
    (hs1 : ∀ x : GL (Fin 2) (w.1.adicCompletion L),
      x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x ∈
          AutomorphicForm.localIntegralSet L w.1 →
        ∫ t : AutomorphicForm.sigmaCentralizer (Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom)
            (diagUnits2 α β), s ((t : GL (Fin 2) (w.1.adicCompletion L)) * x) ∂τ' = 1) :
    ∫ x : GL (Fin 2) (w.1.adicCompletion L),
        (AutomorphicForm.localIntegralSet L w.1).indicator (fun _ => (1 : ℂ))
            (x⁻¹ * diagUnits2 α β * Matrix.GeneralLinearGroup.map θ.toAlgHom.toRingHom x) * (s x : ℂ)
      ∂(AutomorphicForm.localHaar L w.1) =
      if ‖(a : v.adicCompletion K)‖ = 1 ∧ ‖(b : v.adicCompletion K)‖ = 1 then
        (((‖(a : v.adicCompletion K) - (b : v.adicCompletion K)‖⁻¹ : ℝ)) : ℂ)
      else 0 := by sorry
