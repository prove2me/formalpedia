-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/b239c4be-7229-5dc0-885a-ce08be32c9f6
-- title:
--   Integrability of the elliptic kernel diagonal on a determinant slab
-- statement:
--   Let $K$ be a number field, with $\mathbb{A}_K$ its adele ring and $\mathrm{GL}_2(\mathbb{A}_K)$ carrying its Borel $\sigma$-algebra and the associated Haar measure `adelicGLHaar`. Let $\alpha,\beta$ be real numbers with $0 < \alpha$ and $\alpha < \beta$, and write $\mu$ for that Haar measure restricted to the determinant slab $\{g : \|\det g\| \in [\alpha,\beta]\}$, where $\|x\|$ denotes [`NumberField.TateGlobal.ideleNorm`](def/NumberField_TateGlobalZeta.html#L19), the value at the idele $x$ of the distributive Haar character of $\mathbb{A}_K$, viewed as a real number. Let $\Phi \subseteq \mathrm{GL}_2(\mathbb{A}_K)$ be a fundamental domain, in the sense of `MeasureTheory.IsFundamentalDomain`, for the range of the homomorphism $\mathrm{GL}_2(K) \to \mathrm{GL}_2(\mathbb{A}_K)$ induced by $K \to \mathbb{A}_K$, with respect to $\mu$. Let $f : \mathrm{GL}_2(\mathbb{A}_K) \to \mathbb{C}$ be continuous with compact support. Then the function $x \mapsto \sum_{\gamma} f(x^{-1} \gamma x)$, the diagonal of the elliptic part of the adelic kernel, the sum being the `finsum` over those $\gamma \in \mathrm{GL}_2(K)$ whose underlying $2\times 2$ matrix satisfies the predicate `IsEllipticType` and $\gamma$ being regarded in $\mathrm{GL}_2(\mathbb{A}_K)$, is integrable on $\Phi$ with respect to $\mu$.
--
--   This is the convergence of the elliptic term on the geometric side of the trace formula for $\mathrm{GL}_2$ over a number field, in the form of integrability of the elliptic kernel diagonal over a fundamental domain cut out by a bounded determinant slab. It is used in the computation of the elliptic contribution, namely by [`AutomorphicForm.integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab`](thm.html#AutomorphicForm.integrableOn_setIntegral_mul_centralElliptic_adelicKernel_of_isFundamentalDomain_slab) and by [`AutomorphicForm.setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain`](thm.html#AutomorphicForm.setIntegral_centralEllipticFold_eq_finsum_inv_card_mul_integral_setIntegral_centralizerDomain).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_AdelicKernel
import Definitions.Def_NumberField_AdelicHaar
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar

open scoped NumberField

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integrableOn_adelicKernelEllipticPart_diag_of_isFundamentalDomain_slab
    (K : Type) [Field K] [NumberField K] (α β : ℝ) (hα : 0 < α) (hαβ : α < β)
    (Φ : Set (AutomorphicForm.AdelicGL2 (𝓞 K) K))
    (hΦ : IsFundamentalDomain (AutomorphicForm.globalPoints (𝓞 K) K).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (f : AutomorphicForm.AdelicGL2 (𝓞 K) K → ℂ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    IntegrableOn (fun x => AutomorphicForm.adelicKernelEllipticPart K f x x) Φ
      ((adelicGLHaar (Fin 2) (𝓞 K) K).restrict
        {g | NumberField.TateGlobal.ideleNorm K (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) := by sorry
