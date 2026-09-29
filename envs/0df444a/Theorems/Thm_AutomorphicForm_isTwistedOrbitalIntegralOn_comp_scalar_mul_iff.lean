-- Prove2me | Theorems.Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_comp_scalar_mul_iff
-- name    : AutomorphicForm.isTwistedOrbitalIntegralOn_comp_scalar_mul_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.725817+00:00
-- url     : https://prove2.me/theorems/4a309ed1-0a11-53e8-9331-95fe0077732e
-- title:
--   Central translation in twisted orbital integrals
-- statement:
--   Let $K \subseteq L$ be fields with $L$ finite-dimensional over $K$, let $A$ be a commutative topological ring that is a $K$-algebra, and write $E = L \otimes_K A$, equipped throughout with the Borel $\sigma$-algebras coming from its topology. Let $\sigma$ be a $K$-algebra automorphism of $L$, acting on $\mathrm{GL}_2(E)$ entrywise through $\sigma \otimes \mathrm{id}_A$; this action is written $g \mapsto \sigma(g)$. Let $\mu$ be a Borel measure on $\mathrm{GL}_2(E)$, let $c \in E^{\times}$, let $\delta \in \mathrm{GL}_2(E)$, let $\tau'$ be a Borel measure on the twisted centraliser $T_\delta = \{t \in \mathrm{GL}_2(E) : t\,\delta\,\sigma(t)^{-1} = \delta\}$, let $\varphi : \mathrm{GL}_2(E) \to \mathbb{C}$ and $I \in \mathbb{C}$. Assume $T_{c\delta} = T_{\delta}$ as subgroups, where $c$ denotes the scalar matrix $\mathrm{diag}(c,c)$. Then the relation `IsTwistedOrbitalIntegralOn` holds for the data $(\mu, \delta, \tau')$ and test function $g \mapsto \varphi(c\,g)$ with value $I$ if and only if it holds for $(\mu, c\delta, \tau'')$ and test function $\varphi$ with value $I$, where $\tau''$ is the push-forward of $\tau'$ along the identification of $T_\delta$ with $T_{c\delta}$ supplied by the hypothesis. Here the relation for data $(\mu, \delta_0, \tau_0, \psi, I)$ asserts the existence of $w : \mathrm{GL}_2(E) \to \mathbb{R}$ that is nonnegative, measurable and compactly supported, satisfies $\int_{T_{\delta_0}} w(t x)\, d\tau_0 = 1$ for every $x$ with $\psi(x^{-1}\delta_0\,\sigma(x)) \neq 0$, and for which $I = \int \psi(x^{-1}\delta_0\,\sigma(x))\, w(x)\, d\mu$.
--
--   This is the absorption of a central element into the orbital class in the definition of twisted orbital integrals: translating the test function by a central scalar $c$ is the same as translating the twisted conjugacy representative $\delta$ by $c$, with the weight function and the measure on the twisted centraliser unchanged. It is used in the estimate [`AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul`](thm.html#AutomorphicForm.exists_forall_prod_infinitePlace_norm_sub_norm_mul_le_of_isTwistedOrbitalIntegralOn_tensorArch_scalar_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_isTwistedOrbitalIntegralOn_comp_scalar_mul_iff.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open MeasureTheory
open scoped TensorProduct TensorProduct.RightActions

theorem AutomorphicForm.isTwistedOrbitalIntegralOn_comp_scalar_mul_iff
    (K L A : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L]
    [CommRing A] [Algebra K A] [TopologicalSpace A] [IsTopologicalRing A]
    (σ : L ≃ₐ[K] L)
    (μ : @Measure (GL (Fin 2) (L ⊗[K] A)) (AutomorphicForm.glBorelOf (L ⊗[K] A)))
    (c : (L ⊗[K] A)ˣ) (δ : GL (Fin 2) (L ⊗[K] A))
    (τ' : @Measure (AutomorphicForm.twistedCentralizer K L A σ δ) (AutomorphicForm.twistedCentralizerBorel K L A σ δ))
    (φ : GL (Fin 2) (L ⊗[K] A) → ℂ) (I : ℂ)
    (h : AutomorphicForm.twistedCentralizer K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ) =
      AutomorphicForm.twistedCentralizer K L A σ δ) :
    AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ δ τ'
        (fun g => φ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * g)) I ↔
      AutomorphicForm.IsTwistedOrbitalIntegralOn K L A σ μ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ)
        (@Measure.map _ _ (AutomorphicForm.twistedCentralizerBorel K L A σ δ)
          (AutomorphicForm.twistedCentralizerBorel K L A σ (Matrix.GeneralLinearGroup.scalar (Fin 2) c * δ))
          (fun t => ⟨(t : GL (Fin 2) (L ⊗[K] A)), h.symm ▸ t.2⟩) τ')
        φ I := by sorry
