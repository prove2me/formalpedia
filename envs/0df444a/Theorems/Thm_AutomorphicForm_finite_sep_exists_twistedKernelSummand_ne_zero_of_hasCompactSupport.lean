-- Prove2me | Theorems.Thm_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
-- name    : AutomorphicForm.finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:56.265965+00:00
-- url     : https://prove2.me/theorems/b6a99b54-d5e9-568c-9f4a-68fe4213078d
-- title:
--   Finiteness of twisted elliptic and central classes meeting a compact support
-- statement:
--   Let $K$ and $L$ be number fields with $L/K$ Galois, let $\sigma \in \mathrm{Gal}(L/K)$ be such that every $\tau \in \mathrm{Gal}(L/K)$ lies in the subgroup of integer powers of $\sigma$ (so the Galois group is cyclic with generator $\sigma$), and let $D$ be an idelic descent datum for $L/K$: a homomorphism from $\mathrm{Gal}(L/K)$ to the ring automorphisms of the adele ring $\mathbb{A}_L$ of $L$, continuous in each element and compatible with the Galois action on principal adeles. Let $\varphi : GL_2(\mathbb{A}_L) \to \mathbb{C}$ have compact support. Write $I$ for the set of those $\delta \in GL_2(L)$ for which there is a $\gamma \in GL_2(K)$ whose matrix is either central (a scalar multiple of the identity) or elliptic (its characteristic polynomial has no root in $K$), with $\gamma$ representing the conjugacy class in $GL_2(K)$ assigned to the $\sigma$-conjugacy class of $\delta$ by [`LT.TwistedNorm.normClassMap`](def/TwistedNormClasses.html#L766) (the class of a chosen $\sigma$-norm representative of $\delta$ over $K$). Let $R \subseteq I$ be a set such that every $\delta \in I$ satisfies, for exactly one $\delta_0 \in R$, a relation $\delta = u \cdot (h^{-1}\,\delta_0\,\sigma(h))$ with $u \in L^\times$ scalar and $h \in GL_2(L)$, where $\sigma$ acts entrywise. Then the set of $\delta_0 \in R$ for which there exist $x \in GL_2(\mathbb{A}_L)$ and an idele $z \in \mathbb{A}_L^\times$ with $\varphi\bigl(x^{-1}\,\delta_0\,\sigma_{\mathbb{A}}(z\,x)\bigr) \neq 0$ is finite, where $\delta_0$ is viewed in $GL_2(\mathbb{A}_L)$ through principal adeles, $z$ as a central scalar matrix, and $\sigma_{\mathbb{A}}$ is the entrywise automorphism of $GL_2(\mathbb{A}_L)$ induced by $D(\sigma)$.
--
--   This is the twisted analogue of the classical finiteness statement that only finitely many elliptic or central conjugacy classes of $GL_2$ over a number field, taken modulo scalars, meet a fixed compact subset of $GL_2(\mathbb{A})$ up to conjugation and central translation. It is what makes the sum over families with elliptic or central norm in the unfolding of the twisted trace formula a finite sum, and it is used in the project's results on twisted central–elliptic folding and on comparing twisted orbital sums with ordinary ones.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport.lean

import Definitions.Def_AutomorphicForm_SigmaAdelicAction
import Definitions.Def_AutomorphicForm_GL2ConjugacyCells
import Definitions.Def_AutomorphicForm_AdelicLsXi
import Definitions.Def_TwistedNormClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open NumberField

theorem AutomorphicForm.finite_sep_exists_twistedKernelSummand_ne_zero_of_hasCompactSupport
    (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L] [IsGalois K L]
    (σ : L ≃ₐ[K] L) (hgen : ∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ)
    (D : M4aHerbrand.IdeleGaloisDescent (𝓞 L) K L)
    (φ : AutomorphicForm.AdelicGL2 (𝓞 L) L → ℂ) (hφc : HasCompactSupport φ)
    (R : Set (GL (Fin 2) L))
    (hRsub : R ⊆ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ})
    (hR : ∀ δ ∈ {δ : GL (Fin 2) L | ∃ γ : GL (Fin 2) K,
        (γ ∈ AutomorphicForm.ellipticCell K ∨ γ ∈ AutomorphicForm.centralCell K) ∧
        LT.TwistedNorm.normClassMap hgen (LT.TwistedNorm.SigmaConjClasses.mk σ δ) = ConjClasses.mk γ},
      ∃! δ₀ : GL (Fin 2) L, δ₀ ∈ R ∧ ∃ (h : GL (Fin 2) L) (u : Lˣ),
        δ = Matrix.GeneralLinearGroup.scalar (Fin 2) u *
          (h⁻¹ * δ₀ * Matrix.GeneralLinearGroup.map (σ : L →+* L) h)) :
    {δ₀ ∈ R | ∃ (x : AutomorphicForm.AdelicGL2 (𝓞 L) L) (z : (AdeleRing (𝓞 L) L)ˣ),
      φ (x⁻¹ * AutomorphicForm.globalPoints (𝓞 L) L δ₀ *
        AutomorphicForm.sigmaAdelicAct K L D σ (AutomorphicForm.centralScalar (𝓞 L) L z * x)) ≠ 0}.Finite := by sorry
