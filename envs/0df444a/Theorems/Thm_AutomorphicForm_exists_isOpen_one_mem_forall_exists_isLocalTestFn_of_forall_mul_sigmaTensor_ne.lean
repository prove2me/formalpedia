-- Prove2me | Theorems.Thm_AutomorphicForm_exists_isOpen_one_mem_forall_exists_isLocalTestFn_of_forall_mul_sigmaTensor_ne
-- name    : AutomorphicForm.exists_isOpen_one_mem_forall_exists_isLocalTestFn_of_forall_mul_sigmaTensor_ne
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:54.893446+00:00
-- url     : https://prove2.me/theorems/58785356-e507-5a30-a52e-6e8ed56a10c2
-- title:
--   Local transfer near an anisotropic base point
-- statement:
--   Let $K \subseteq L$ be number fields with $[L:K]=2$, let $\sigma$ be a non-trivial $K$-algebra automorphism of $L$, and let $v$ be a nonzero prime of $\mathcal{O}_K$ such that there is no $K$-algebra map $L \to K_v$, where $K_v$ denotes the $v$-adic completion. Let $l \in K_v^\times$ be such that no $x \in L \otimes_K K_v$ satisfies $x \cdot (\sigma \otimes \mathrm{id})(x) = l$, let $g \in \mathrm{GL}_2(K_v)$ have matrix $\begin{pmatrix} 0 & 1 \\ l & 0\end{pmatrix}$, and let $\beta \in \mathrm{GL}_2(L \otimes_K K_v)$ be its image under the map induced by $a \mapsto 1 \otimes a$. Then there is a subset $W$ of the twisted centraliser $\{t : t\beta\,\sigma(t)^{-1} = \beta\}$ of $\beta$ (with $\sigma$ acting entrywise through $\sigma \otimes \mathrm{id}$) which is open and contains $1$, with the following property. Let $\varphi_v : \mathrm{GL}_2(L \otimes_K K_v) \to \mathbb{C}$ be locally constant with compact support and suppose $\mathrm{tsupport}\,\varphi_v$ is contained in the set of elements of the form $x^{-1}(t\beta)\sigma(x)$ with $t \in W$. Then there is a locally constant, compactly supported $f_v : \mathrm{GL}_2(K_v) \to \mathbb{C}$ such that: (i) for every $t \in W$ and $\delta_1 = t\beta$ whose norm string $\delta_1 \cdot \sigma(\delta_1)$ is regular semisimple (its $\mathrm{tr}^2 - 4\det$ is a unit), every regular semisimple $\gamma \in \mathrm{GL}_2(K_v)$, every $y$ with $\gamma = y^{-1}(\delta_1\sigma(\delta_1))y$ after base change, and every pair of Haar measures $\tau$ on the centraliser of $\gamma$ and $\tau'$ on the twisted centraliser of $\delta_1$ (Borel $\sigma$-algebras) that are coupled through $y$, any twisted orbital integral $I'$ of $\varphi_v$ at $\delta_1$ for `semiLocalHaar` and $\tau'$ equals any orbital integral $I$ of $f_v$ at $\gamma$ for `localHaar` and $\tau$; and (ii) for every regular semisimple $\gamma \in \mathrm{GL}_2(K_v)$ that is the norm of no element of $\mathrm{tsupport}\,\varphi_v$, every orbital integral of $f_v$ at $\gamma$ against a Haar measure on the centraliser of $\gamma$ vanishes.
--
--   This is the local matching (transfer) of test functions for quadratic base change of $\mathrm{GL}(2)$ at a place $v$ of $K$ that does not split in $L$, in a neighbourhood of a base point $\beta$ whose norm is not regular semisimple, the twisted centraliser there being the unit group of a quaternion division algebra over $K_v$. It supplies the anisotropic case in the proofs of [`AutomorphicForm.exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_not_isRegularSemisimple_normString`](thm.html#AutomorphicForm.exists_nhds_forall_exists_isLocalTestFn_areMatchingLocal_of_not_isRegularSemisimple_normString) and [`AutomorphicForm.exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime`](thm.html#AutomorphicForm.exists_nhds_forall_exists_areMatchingLocal_and_central_of_not_isRegularSemisimple_normString_of_prime).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_isOpen_one_mem_forall_exists_isLocalTestFn_of_forall_mul_sigmaTensor_ne.lean

import Definitions.Def_AutomorphicForm_TwistedOrbital

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField IsDedekindDomain
open scoped TensorProduct TensorProduct.RightActions

theorem
AutomorphicForm.exists_isOpen_one_mem_forall_exists_isLocalTestFn_of_forall_mul_sigmaTensor_ne
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    (h2 : Module.finrank K L = 2) (σ : L ≃ₐ[K] L) (hσ : σ ≠ 1)
    (v : HeightOneSpectrum (𝓞 K)) (hι : IsEmpty (L →ₐ[K] v.adicCompletion K)) (l : (v.adicCompletion K)ˣ)
    (hl : ∀ x : L ⊗[K] v.adicCompletion K,
      x * AutomorphicForm.sigmaTensor K L (v.adicCompletion K) σ x ≠
        algebraMap (v.adicCompletion K) (L ⊗[K] v.adicCompletion K) (l : v.adicCompletion K))
    (g : GL (Fin 2) (v.adicCompletion K))
    (hg : (g : Matrix (Fin 2) (Fin 2) (v.adicCompletion K)) = !![0, 1; (l : v.adicCompletion K), 0])
    (β : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) (hβ : β = AutomorphicForm.toTensorGL K L (v.adicCompletion K) g) :
    ∃ W : Set (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ β),
      IsOpen W ∧ (1 : AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ β) ∈ W ∧
      ∀ φv : GL (Fin 2) (L ⊗[K] v.adicCompletion K) → ℂ, AutomorphicForm.IsSemiLocalTestFn K L v φv →
        tsupport φv ⊆
          {δ' | ∃ t ∈ W,
            AutomorphicForm.IsSigmaConjugate K L (v.adicCompletion K) σ
              ((t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * β) δ'} →
        ∃ fv : GL (Fin 2) (v.adicCompletion K) → ℂ, AutomorphicForm.IsLocalTestFn K v fv ∧
          (∀ t ∈ W, ∀ δ₁ : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              δ₁ = (t : GL (Fin 2) (L ⊗[K] v.adicCompletion K)) * β →
            AutomorphicForm.IsRegularSemisimple (AutomorphicForm.normString K L (v.adicCompletion K) σ δ₁) →
            ∀ γ : GL (Fin 2) (v.adicCompletion K), AutomorphicForm.IsRegularSemisimple γ →
            ∀ y : GL (Fin 2) (L ⊗[K] v.adicCompletion K),
              AutomorphicForm.IsNormConjugator K L (v.adicCompletion K) σ γ δ₁ y →
            ∀ (τ : @MeasureTheory.Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
                (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ))
              (τ' : @MeasureTheory.Measure (AutomorphicForm.twistedCentralizer K L (v.adicCompletion K) σ δ₁)
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁)),
              @MeasureTheory.Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ →
              @MeasureTheory.Measure.IsHaarMeasure _ _ _
                (AutomorphicForm.twistedCentralizerBorel K L (v.adicCompletion K) σ δ₁) τ' →
              AutomorphicForm.Coupled K L (v.adicCompletion K) σ γ δ₁ y τ τ' →
              ∀ I I' : ℂ,
                AutomorphicForm.IsTwistedOrbitalIntegralOn K L (v.adicCompletion K) σ
                  (AutomorphicForm.semiLocalHaar K L v) δ₁ τ' φv I' →
                AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ fv I →
                I' = I) ∧
          ∀ γ : GL (Fin 2) (v.adicCompletion K), AutomorphicForm.IsRegularSemisimple γ →
            (¬ ∃ δ ∈ tsupport φv, AutomorphicForm.IsNormOf K L (v.adicCompletion K) σ γ δ) →
            ∀ τ : @MeasureTheory.Measure (Subgroup.centralizer ({γ} : Set (GL (Fin 2) (v.adicCompletion K))))
              (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ),
              @MeasureTheory.Measure.IsHaarMeasure _ _ _ (AutomorphicForm.centralizerBorel (v.adicCompletion K) γ) τ →
              ∀ I : ℂ,
                AutomorphicForm.IsOrbitalIntegralOn (v.adicCompletion K) (AutomorphicForm.localHaar K v) γ τ fv I →
                I = 0 := by sorry
