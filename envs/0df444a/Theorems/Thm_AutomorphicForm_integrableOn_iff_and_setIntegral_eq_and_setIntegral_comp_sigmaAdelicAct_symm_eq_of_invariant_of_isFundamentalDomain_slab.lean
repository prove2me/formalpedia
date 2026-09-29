-- Prove2me | Theorems.Thm_AutomorphicForm_integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab
-- name    : AutomorphicForm.integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/e7b97878-821a-51c0-99bb-4529e6199c6d
-- title:
--   Change of fundamental domain in a determinant slab
-- statement:
--   Let $K \subseteq L$ be number fields, let $D$ be an idele Galois descent datum for $L/K$ — a monoid homomorphism $\sigma \mapsto D.\mathrm{act}\,\sigma$ from $\mathrm{Aut}_K(L)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$, compatible with $\mathbb{A}_L \leftarrow L$ and continuous in each $\sigma$ — and let $\sigma$ be a $K$-automorphism of $L$; write $\sigma_{\mathbb{A}}$ for [`AutomorphicForm.sigmaAdelicAct K L D σ`](def/AutomorphicForm_SigmaAdelicAction.html#L14), the entrywise application of $D.\mathrm{act}\,\sigma$ to $\mathrm{GL}_2(\mathbb{A}_L)$, and $\iota$ for `globalPoints`, the entrywise map $\mathrm{GL}_2(L) \to \mathrm{GL}_2(\mathbb{A}_L)$. Let $\alpha,\beta \in \mathbb{R}$ and let $S = \{g : \|\det g\| \in [\alpha,\beta]\}$ be the corresponding determinant slab, the idele norm $\|\cdot\|$ being the distributive Haar character of $\mathbb{A}_L$. Let $\Phi, \Phi_0 \subseteq S$ each be a fundamental domain for the action of the image of $\iota$ on $\mathrm{GL}_2(\mathbb{A}_L)$ with respect to the adelic Haar measure $\mu$ of $\mathrm{GL}_2(\mathbb{A}_L)$ restricted to $S$. Let $E$ be a real normed space, $F : \mathrm{GL}_2(\mathbb{A}_L) \to E$ satisfy $F(\iota\gamma \cdot x) = F(x)$ for all $\gamma, x$, and $G$ a two-variable kernel with $G(\iota\gamma \cdot x, y) = G(x,y)$ and $G(x, \iota\gamma \cdot y) = G(x,y)$. Then: $F$ is $\mu$-integrable on $\Phi_0$ iff on $\Phi$; $\int_{\Phi_0} F \,d\mu = \int_{\Phi} F \,d\mu$ (Bochner integrals, no integrability assumed); $\sigma_{\mathbb{A}}(\Phi_0)$ is again such a fundamental domain for $\mu$ restricted to $S$; $x \mapsto G(x, \sigma_{\mathbb{A}}^{-1}x)$ is integrable on $\Phi_0$ iff $x \mapsto G(\sigma_{\mathbb{A}}x, x)$ is integrable on $\Phi$; and $\int_{\Phi_0} G(x,\sigma_{\mathbb{A}}^{-1}x)\,d\mu = \int_{\Phi} G(\sigma_{\mathbb{A}}x,x)\,d\mu$.
--
--   This is the change-of-fundamental-domain lemma for integrals of left $\mathrm{GL}_2(L)$-invariant functions over a slab $\alpha \le \|\det\| \le \beta$ in $\mathrm{GL}_2(\mathbb{A}_L)$, together with its twisted form along the graph of the Galois action, which lets the twisted diagonal be read on either side of $\sigma_{\mathbb{A}}$. It is invoked by the base-change trace computations for cuspidal isotypic components and for the twisted cut trace at principal level, where a fundamental domain is chosen anew at each step. Inputs are that $\sigma_{\mathbb{A}}$ preserves the adelic Haar measure and the idele norm of the determinant, that $\|\det \iota\gamma\| = 1$, and continuity of $g \mapsto \|\det g\|$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab.lean

import Definitions.Def_AutomorphicForm_IsotypicCuspSpace
import Definitions.Def_NumberField_TateGlobalZeta

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory NumberField NumberField.AdelicHaar
open IsDedekindDomain

attribute [local instance] NumberField.AdelicHaar.glBorel

theorem AutomorphicForm.integrableOn_iff_and_setIntegral_eq_and_setIntegral_comp_sigmaAdelicAct_symm_eq_of_invariant_of_isFundamentalDomain_slab
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L) (σ : L ≃ₐ[K] L)
    (α β : ℝ) (Φ Φ₀ : Set (AdelicGL2 (𝓞 L) L))
    (hΦs : Φ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (hΦ₀s : Φ₀ ⊆ {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β})
    (hΦ₀ : IsFundamentalDomain (globalPoints (𝓞 L) L).range Φ₀
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}))
    (E : Type) [NormedAddCommGroup E] [NormedSpace ℝ E]
    (F : AdelicGL2 (𝓞 L) L → E)
    (hF : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x : AdelicGL2 (𝓞 L) L),
      F (globalPoints (𝓞 L) L γ * x) = F x)
    (G : AdelicGL2 (𝓞 L) L → AdelicGL2 (𝓞 L) L → E)
    (hG₁ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x y : AdelicGL2 (𝓞 L) L),
      G (globalPoints (𝓞 L) L γ * x) y = G x y)
    (hG₂ : ∀ (γ : Matrix.GeneralLinearGroup (Fin 2) L) (x y : AdelicGL2 (𝓞 L) L),
      G x (globalPoints (𝓞 L) L γ * y) = G x y) :
    (IntegrableOn F Φ₀ (adelicGLHaar (Fin 2) (𝓞 L) L) ↔ IntegrableOn F Φ (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
    (∫ x in Φ₀, F x ∂adelicGLHaar (Fin 2) (𝓞 L) L = ∫ x in Φ, F x ∂adelicGLHaar (Fin 2) (𝓞 L) L) ∧
    IsFundamentalDomain (globalPoints (𝓞 L) L).range (AutomorphicForm.sigmaAdelicAct K L D σ '' Φ₀)
      ((adelicGLHaar (Fin 2) (𝓞 L) L).restrict
        {g | NumberField.TateGlobal.ideleNorm L (Matrix.GeneralLinearGroup.det g) ∈ Set.Icc α β}) ∧
    (IntegrableOn (fun x => G x (AutomorphicForm.sigmaAdelicAct K L D σ.symm x)) Φ₀
        (adelicGLHaar (Fin 2) (𝓞 L) L) ↔
      IntegrableOn (fun x => G (AutomorphicForm.sigmaAdelicAct K L D σ x) x) Φ
        (adelicGLHaar (Fin 2) (𝓞 L) L)) ∧
    (∫ x in Φ₀, G x (AutomorphicForm.sigmaAdelicAct K L D σ.symm x) ∂adelicGLHaar (Fin 2) (𝓞 L) L =
      ∫ x in Φ, G (AutomorphicForm.sigmaAdelicAct K L D σ x) x ∂adelicGLHaar (Fin 2) (𝓞 L) L) := by sorry
